from collections import defaultdict
import base64
import json
import struct
import zlib
from datetime import date, datetime, timedelta, timezone
import os
import sys
from typing import Any, Dict, List, Optional, Tuple

import boto3
import requests
from botocore.exceptions import BotoCoreError, ClientError, NoCredentialsError


try:
    from dotenv import load_dotenv

    load_dotenv()
except ImportError:
    pass


DEFAULT_REPORT_DAYS = 7
DEFAULT_TOP_SERVICES = 10
DEFAULT_COST_AGGREGATION = "UnblendedCost"
DEFAULT_GROUP_BY = "SERVICE"
MIN_TREND_DAYS = 7
TREND_WIDTH = 14
TREND_HEIGHT = 4
ROW_CHART_WIDTH = 96
ROW_CHART_HEIGHT = 24
MAIN_CHART_WIDTH = 220
MAIN_CHART_HEIGHT = 70
MAX_TEAMS_MESSAGE_BYTES = 28 * 1024

COST_EXPLORER_REGION = "us-east-1"
HTTP_TIMEOUT_SECONDS = 20


ReportRow = Dict[str, Any]
ReportData = Dict[str, Any]


def get_required_env(name: str) -> str:
    value = os.environ.get(name)

    if value is None or not value.strip():
        raise ValueError(f"Required environment variable is missing: {name}")

    return value.strip()


def get_positive_int_env(name: str, default: int) -> int:
    raw_value = os.environ.get(name, str(default))

    try:
        value = int(raw_value)
    except ValueError as error:
        raise ValueError(
            f"{name} must be an integer, received: {raw_value}"
        ) from error

    if value <= 0:
        raise ValueError(f"{name} must be greater than zero")

    return value


def _draw_line_on_canvas(
    canvas: List[List[bool]],
    x0: int,
    y0: int,
    x1: int,
    y1: int,
) -> None:
    """Draw a connected line using Bresenham's algorithm."""
    dx = abs(x1 - x0)
    sx = 1 if x0 < x1 else -1
    dy = -abs(y1 - y0)
    sy = 1 if y0 < y1 else -1
    error = dx + dy

    while True:
        if 0 <= y0 < len(canvas) and 0 <= x0 < len(canvas[0]):
            canvas[y0][x0] = True

        if x0 == x1 and y0 == y1:
            break

        doubled_error = 2 * error

        if doubled_error >= dy:
            error += dy
            x0 += sx

        if doubled_error <= dx:
            error += dx
            y0 += sy


def _braille_character(block: List[List[bool]]) -> str:
    """Convert a 2x4 boolean pixel block into one Unicode Braille cell."""
    dot_positions = {
        (0, 0): 0,
        (0, 1): 1,
        (0, 2): 2,
        (1, 0): 3,
        (1, 1): 4,
        (1, 2): 5,
        (0, 3): 6,
        (1, 3): 7,
    }

    bits = 0

    for (x, y), bit_number in dot_positions.items():
        if block[y][x]:
            bits |= 1 << bit_number

    return chr(0x2800 + bits)


def sparkline(
    datapoints: List[float],
    width: int = TREND_WIDTH,
) -> str:
    """Create a connected Braille line chart suitable for Teams text blocks.

    The chart uses min/max normalization so small daily differences stay visible.
    Unlike block characters, the Braille canvas produces a connected line shape.
    """
    if not datapoints:
        return "─" * max(width, 1)

    values = [max(float(datapoint), 0.0) for datapoint in datapoints]
    width = max(int(width), 2)
    pixel_width = width * 2
    pixel_height = TREND_HEIGHT

    minimum = min(values)
    maximum = max(values)

    if len(values) == 1:
        values = [values[0], values[0]]

    points: List[Tuple[int, int]] = []

    for index, value in enumerate(values):
        x_position = round(
            index * (pixel_width - 1) / max(len(values) - 1, 1)
        )

        if maximum == minimum:
            y_position = pixel_height // 2
        else:
            normalized = (value - minimum) / (maximum - minimum)
            y_position = round(
                (1.0 - normalized) * (pixel_height - 1)
            )

        points.append((x_position, y_position))

    canvas = [
        [False for _ in range(pixel_width)]
        for _ in range(pixel_height)
    ]

    for point_index in range(len(points) - 1):
        x0, y0 = points[point_index]
        x1, y1 = points[point_index + 1]
        _draw_line_on_canvas(canvas, x0, y0, x1, y1)

    if points:
        last_x, last_y = points[-1]
        canvas[last_y][last_x] = True

    characters: List[str] = []

    for block_start in range(0, pixel_width, 2):
        block = [
            [
                canvas[row][block_start + column]
                for column in range(2)
            ]
            for row in range(pixel_height)
        ]
        characters.append(_braille_character(block))

    return "".join(characters)

def calculate_change_percent(
    previous_cost: float,
    current_cost: float,
) -> Optional[float]:
    """Calculate day-over-day percentage change from exact AWS amounts.

    AWS amounts are kept at full precision for the calculation. Rounding is
    applied only when values are displayed in Teams.
    """
    previous = float(previous_cost)
    current = float(current_cost)
    zero_tolerance = 1e-12

    if abs(previous) <= zero_tolerance:
        if abs(current) <= zero_tolerance:
            return 0.0
        return None

    return ((current - previous) / previous) * 100.0

def delta(costs: List[float]) -> Optional[float]:
    if len(costs) < 2:
        return 0.0

    return calculate_change_percent(
        previous_cost=costs[-2],
        current_cost=costs[-1],
    )


def format_change(
    previous_cost: float,
    current_cost: float,
) -> Tuple[str, str]:
    """Return readable daily change text and its Adaptive Card color."""
    percentage = calculate_change_percent(previous_cost, current_cost)

    if percentage is None:
        return "New spend  ↑", "Attention"

    if percentage > 0:
        return f"+{percentage:,.2f}%  ↑", "Attention"

    if percentage < 0:
        return f"−{abs(percentage):,.2f}%  ↓", "Good"

    return "0.00%  —", "Default"

def format_console_change(costs: List[float]) -> str:
    if len(costs) < 2:
        return "0.00%"

    change_text, _ = format_change(costs[-2], costs[-1])
    return change_text


def format_money(value: float) -> str:
    return f"US${float(value):,.2f}"



def _png_chunk(chunk_type: bytes, data: bytes) -> bytes:
    return (
        struct.pack(">I", len(data))
        + chunk_type
        + data
        + struct.pack(">I", zlib.crc32(chunk_type + data) & 0xFFFFFFFF)
    )


def _set_pixel(
    pixels: List[List[List[int]]],
    x: int,
    y: int,
    color: Tuple[int, int, int, int],
) -> None:
    if y < 0 or y >= len(pixels) or x < 0 or x >= len(pixels[0]):
        return

    source_red, source_green, source_blue, source_alpha = color
    target_red, target_green, target_blue, target_alpha = pixels[y][x]

    alpha = source_alpha / 255.0
    inverse_alpha = 1.0 - alpha

    pixels[y][x] = [
        round(source_red * alpha + target_red * inverse_alpha),
        round(source_green * alpha + target_green * inverse_alpha),
        round(source_blue * alpha + target_blue * inverse_alpha),
        min(255, round(source_alpha + target_alpha * inverse_alpha)),
    ]


def _draw_png_line(
    pixels: List[List[List[int]]],
    x0: int,
    y0: int,
    x1: int,
    y1: int,
    color: Tuple[int, int, int, int],
    thickness: int = 1,
) -> None:
    dx = abs(x1 - x0)
    sx = 1 if x0 < x1 else -1
    dy = -abs(y1 - y0)
    sy = 1 if y0 < y1 else -1
    error = dx + dy

    while True:
        radius = max(thickness // 2, 0)
        for offset_y in range(-radius, radius + 1):
            for offset_x in range(-radius, radius + 1):
                _set_pixel(pixels, x0 + offset_x, y0 + offset_y, color)

        if x0 == x1 and y0 == y1:
            break

        doubled_error = 2 * error

        if doubled_error >= dy:
            error += dy
            x0 += sx

        if doubled_error <= dx:
            error += dx
            y0 += sy


def _draw_png_circle(
    pixels: List[List[List[int]]],
    center_x: int,
    center_y: int,
    radius: int,
    color: Tuple[int, int, int, int],
) -> None:
    radius_squared = radius * radius

    for y in range(center_y - radius, center_y + radius + 1):
        for x in range(center_x - radius, center_x + radius + 1):
            if (x - center_x) ** 2 + (y - center_y) ** 2 <= radius_squared:
                _set_pixel(pixels, x, y, color)


def _encode_rgba_png(pixels: List[List[List[int]]]) -> bytes:
    height = len(pixels)
    width = len(pixels[0]) if height else 0

    raw_rows = bytearray()
    for row in pixels:
        raw_rows.append(0)
        for red, green, blue, alpha in row:
            raw_rows.extend((red, green, blue, alpha))

    signature = b"\x89PNG\r\n\x1a\n"
    header = struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0)

    return (
        signature
        + _png_chunk(b"IHDR", header)
        + _png_chunk(b"IDAT", zlib.compress(bytes(raw_rows), level=9))
        + _png_chunk(b"IEND", b"")
    )


def chart_data_uri(
    datapoints: List[float],
    width: int,
    height: int,
    color_name: str,
    show_grid: bool = False,
) -> str:
    values = [max(float(value), 0.0) for value in datapoints]

    if not values:
        values = [0.0, 0.0]
    elif len(values) == 1:
        values = [values[0], values[0]]

    colors = {
        "Attention": (238, 91, 91, 255),
        "Good": (98, 203, 118, 255),
        "Accent": (124, 170, 255, 255),
        "Default": (222, 226, 232, 255),
    }
    line_color = colors.get(color_name, colors["Default"])
    fill_color = (*line_color[:3], 42)
    grid_color = (180, 188, 198, 38)
    point_color = (248, 250, 252, 255)

    pixels: List[List[List[int]]] = [
        [[0, 0, 0, 0] for _ in range(width)]
        for _ in range(height)
    ]

    left_padding = 4
    right_padding = 6
    top_padding = 5
    bottom_padding = 5
    chart_width = max(width - left_padding - right_padding, 2)
    chart_height = max(height - top_padding - bottom_padding, 2)

    if show_grid:
        for fraction in (0.25, 0.5, 0.75):
            grid_y = top_padding + round(chart_height * fraction)
            for x in range(left_padding, width - right_padding):
                if x % 3 != 0:
                    _set_pixel(pixels, x, grid_y, grid_color)

    minimum = min(values)
    maximum = max(values)
    points: List[Tuple[int, int]] = []

    for index, value in enumerate(values):
        x = left_padding + round(
            index * (chart_width - 1) / max(len(values) - 1, 1)
        )

        if maximum == minimum:
            y = top_padding + chart_height // 2
        else:
            normalized = (value - minimum) / (maximum - minimum)
            y = top_padding + round((1.0 - normalized) * (chart_height - 1))

        points.append((x, y))

    baseline = height - bottom_padding
    for x, y in points:
        for fill_y in range(y + 1, baseline):
            _set_pixel(pixels, x, fill_y, fill_color)

    line_thickness = 2 if height >= 50 else 1
    for index in range(len(points) - 1):
        x0, y0 = points[index]
        x1, y1 = points[index + 1]
        _draw_png_line(
            pixels,
            x0,
            y0,
            x1,
            y1,
            line_color,
            thickness=line_thickness,
        )

    point_radius = 2 if height >= 50 else 1
    for x, y in points:
        _draw_png_circle(pixels, x, y, point_radius, point_color)

    last_x, last_y = points[-1]
    if height >= 50:
        _draw_png_circle(pixels, last_x, last_y, 6, line_color)
        _draw_png_circle(pixels, last_x, last_y, 3, point_color)

    encoded = base64.b64encode(_encode_rgba_png(pixels)).decode("ascii")
    return f"data:image/png;base64,{encoded}"


def find_by_key(
    values: List[Dict[str, Any]],
    key: str,
    value: str,
) -> Optional[Dict[str, Any]]:
    for item in values:
        if item.get(key) == value:
            return item

    return None


def load_aws_accounts() -> List[Dict[str, Optional[str]]]:
    account_count = get_positive_int_env("AWS_ACCOUNT_COUNT", 1)

    default_region = os.environ.get(
        "AWS_REGION",
        COST_EXPLORER_REGION,
    ).strip()

    accounts: List[Dict[str, Optional[str]]] = []

    for index in range(1, account_count + 1):
        prefix = f"AWS_ACCOUNT_{index}"

        account_name = get_required_env(f"{prefix}_NAME")
        access_key_id = get_required_env(f"{prefix}_ACCESS_KEY_ID")
        secret_access_key = get_required_env(f"{prefix}_SECRET_ACCESS_KEY")
        session_token = os.environ.get(f"{prefix}_SESSION_TOKEN")
        region = os.environ.get(
            f"{prefix}_REGION",
            default_region,
        ).strip()

        accounts.append(
            {
                "name": account_name,
                "access_key_id": access_key_id,
                "secret_access_key": secret_access_key,
                "session_token": (
                    session_token.strip() if session_token else None
                ),
                "region": region,
                "expected_account_id": (
                    os.environ.get(f"{prefix}_ID", "").strip() or None
                ),
            }
        )

    return accounts


def create_aws_session(
    account: Dict[str, Optional[str]],
) -> boto3.Session:
    return boto3.Session(
        aws_access_key_id=account["access_key_id"],
        aws_secret_access_key=account["secret_access_key"],
        aws_session_token=account.get("session_token"),
        region_name=account.get("region") or COST_EXPLORER_REGION,
    )


def calculate_billing_period(
    report_days: int,
    end_date_text: Optional[str] = None,
) -> Tuple[date, date, date]:
    if end_date_text:
        try:
            end_date = datetime.strptime(
                end_date_text,
                "%Y-%m-%d",
            ).date()
        except ValueError as error:
            raise ValueError(
                "BILLING_END_DATE must use YYYY-MM-DD format"
            ) from error
    else:
        end_date = datetime.now(timezone.utc).date()

    start_date = end_date - timedelta(days=report_days)
    report_date = end_date - timedelta(days=1)

    return start_date, end_date, report_date


def get_cost_filter() -> Dict[str, Any]:
    return {
        "Not": {
            "Dimensions": {
                "Key": "RECORD_TYPE",
                "Values": [
                    "Credit",
                    "Refund",
                    "Upfront",
                    "Support",
                ],
            }
        }
    }


def get_forecast_metric(cost_aggregation: str) -> str:
    metric_map = {
        "BlendedCost": "BLENDED_COST",
        "UnblendedCost": "UNBLENDED_COST",
        "AmortizedCost": "AMORTIZED_COST",
        "NetUnblendedCost": "NET_UNBLENDED_COST",
        "NetAmortizedCost": "NET_AMORTIZED_COST",
    }

    return metric_map.get(cost_aggregation, "UNBLENDED_COST")


def get_cost_and_usage_all_pages(
    client: Any,
    query: Dict[str, Any],
) -> Dict[str, Any]:
    """Read every Cost Explorer page and merge periods by start date."""
    periods_by_start: Dict[str, Dict[str, Any]] = {}
    dimension_attributes: List[Dict[str, Any]] = []
    next_page_token: Optional[str] = None

    while True:
        request = dict(query)
        if next_page_token:
            request["NextPageToken"] = next_page_token

        response = client.get_cost_and_usage(**request)
        dimension_attributes.extend(
            response.get("DimensionValueAttributes", [])
        )

        for period in response.get("ResultsByTime", []):
            period_start = str(
                period.get("TimePeriod", {}).get("Start", "")
            )
            if not period_start:
                continue

            merged = periods_by_start.setdefault(
                period_start,
                {
                    "TimePeriod": dict(period.get("TimePeriod", {})),
                    "Total": {},
                    "Groups": [],
                    "Estimated": False,
                },
            )
            merged["Estimated"] = bool(
                merged.get("Estimated", False)
                or period.get("Estimated", False)
            )
            if period.get("Total"):
                merged["Total"] = dict(period.get("Total", {}))
            merged["Groups"].extend(period.get("Groups", []))

        next_page_token = response.get("NextPageToken")
        if not next_page_token:
            break

    return {
        "ResultsByTime": [
            periods_by_start[key]
            for key in sorted(periods_by_start)
        ],
        "DimensionValueAttributes": dimension_attributes,
    }


def verify_aws_identity(
    session: boto3.Session,
    account_name: str,
    expected_account_id: Optional[str] = None,
) -> str:
    """Log and optionally validate the AWS account used by the credentials."""
    identity = session.client("sts").get_caller_identity()
    actual_account_id = str(identity.get("Account", ""))
    arn = str(identity.get("Arn", ""))

    if not actual_account_id:
        raise RuntimeError(
            f"Unable to identify AWS account for {account_name}"
        )

    if expected_account_id and actual_account_id != expected_account_id:
        raise RuntimeError(
            f"AWS account mismatch for {account_name}: expected "
            f"{expected_account_id}, credentials belong to "
            f"{actual_account_id}"
        )

    print(
        f"Verified AWS identity for {account_name}: "
        f"account={actual_account_id}, arn={arn}"
    )
    return actual_account_id


def get_daily_totals_from_aws(
    client: Any,
    start_date: date,
    end_date: date,
    cost_aggregation: str,
) -> Tuple[Dict[str, float], Dict[str, bool]]:
    """Fetch authoritative ungrouped daily totals directly from AWS."""
    response = get_cost_and_usage_all_pages(
        client=client,
        query={
            "TimePeriod": {
                "Start": start_date.isoformat(),
                "End": end_date.isoformat(),
            },
            "Granularity": "DAILY",
            "Filter": get_cost_filter(),
            "Metrics": [cost_aggregation],
        },
    )

    totals: Dict[str, float] = {}
    estimated: Dict[str, bool] = {}

    for period in response.get("ResultsByTime", []):
        period_start = str(
            period.get("TimePeriod", {}).get("Start", "")
        )
        if not period_start:
            continue

        amount = (
            period.get("Total", {})
            .get(cost_aggregation, {})
            .get("Amount", "0")
        )
        totals[period_start] = float(amount)
        estimated[period_start] = bool(period.get("Estimated", False))

    return totals, estimated


def get_total_cost_for_period(
    client: Any,
    start_date: date,
    end_date: date,
    cost_aggregation: str,
) -> Tuple[float, bool]:
    """Return an AWS ungrouped total and whether AWS marks it estimated."""
    if start_date >= end_date:
        return 0.0, False

    result = get_cost_and_usage_all_pages(
        client=client,
        query={
            "TimePeriod": {
                "Start": start_date.isoformat(),
                "End": end_date.isoformat(),
            },
            "Granularity": "MONTHLY",
            "Filter": get_cost_filter(),
            "Metrics": [cost_aggregation],
        },
    )

    total_cost = 0.0
    is_estimated = False

    for period in result.get("ResultsByTime", []):
        amount = (
            period.get("Total", {})
            .get(cost_aggregation, {})
            .get("Amount", "0")
        )
        total_cost += float(amount)
        is_estimated = bool(
            is_estimated or period.get("Estimated", False)
        )

    return total_cost, is_estimated

def get_monthly_cost_overview(
    session: boto3.Session,
    cost_aggregation: str,
    end_date_text: Optional[str] = None,
) -> Dict[str, Any]:
    """Fetch current/previous month costs and forecast directly from AWS.

    The month-end forecast is the exact Total.Amount returned by the AWS
    Cost Explorer GetCostForecast API. No fixed value, local run-rate, or
    month-to-date addition is applied.
    """
    today_utc = datetime.now(timezone.utc).date()

    if end_date_text:
        try:
            as_of_date = datetime.strptime(
                end_date_text,
                "%Y-%m-%d",
            ).date()
        except ValueError as error:
            raise ValueError(
                "BILLING_END_DATE must use YYYY-MM-DD format"
            ) from error

        if as_of_date != today_utc:
            raise ValueError(
                "AWS Cost Explorer forecast is current-data only. "
                "Remove BILLING_END_DATE to use the live AWS forecast."
            )
    else:
        as_of_date = today_utc

    current_month_start = date(as_of_date.year, as_of_date.month, 1)

    if as_of_date.month == 12:
        next_month_start = date(as_of_date.year + 1, 1, 1)
    else:
        next_month_start = date(as_of_date.year, as_of_date.month + 1, 1)

    if current_month_start.month == 1:
        previous_month_start = date(current_month_start.year - 1, 12, 1)
    else:
        previous_month_start = date(
            current_month_start.year,
            current_month_start.month - 1,
            1,
        )

    client = session.client("ce", region_name=COST_EXPLORER_REGION)

    current_month_cost, current_month_estimated = (
        get_total_cost_for_period(
            client=client,
            start_date=current_month_start,
            end_date=as_of_date,
            cost_aggregation=cost_aggregation,
        )
    )

    previous_month_cost, previous_month_estimated = (
        get_total_cost_for_period(
            client=client,
            start_date=previous_month_start,
            end_date=current_month_start,
            cost_aggregation=cost_aggregation,
        )
    )

    try:
        forecast_result = client.get_cost_forecast(
            TimePeriod={
                "Start": as_of_date.isoformat(),
                "End": next_month_start.isoformat(),
            },
            Metric=get_forecast_metric(cost_aggregation),
            Granularity="MONTHLY",
            Filter=get_cost_filter(),
        )
    except (ClientError, BotoCoreError) as error:
        raise RuntimeError(
            "AWS Cost Explorer forecast is unavailable; no local or "
            f"hard-coded forecast was substituted: {error}"
        ) from error

    forecast_month_end = float(
        forecast_result.get("Total", {}).get("Amount", "0")
    )
    forecast_remaining = max(
        forecast_month_end - current_month_cost,
        0.0,
    )

    if previous_month_cost == 0.0:
        forecast_change_percent = None
    else:
        forecast_change_percent = (
            (forecast_month_end / previous_month_cost) - 1
        ) * 100.0

    print(
        "AWS monthly values | "
        f"actual {current_month_start.isoformat()} to "
        f"{as_of_date.isoformat()} (end exclusive)="
        f"{format_money(current_month_cost)}, "
        f"AWS forecast month end={format_money(forecast_month_end)}, "
        f"derived remaining forecast={format_money(forecast_remaining)}"
    )

    return {
        "current_month_cost": current_month_cost,
        "forecast_month_end": forecast_month_end,
        "forecast_remaining": forecast_remaining,
        "previous_month_cost": previous_month_cost,
        "forecast_change_percent": forecast_change_percent,
        "current_month_label": current_month_start.strftime("%B %Y"),
        "previous_month_label": previous_month_start.strftime("%B %Y"),
        "forecast_source": "AWS Cost Explorer forecast",
        "current_month_estimated": current_month_estimated,
        "previous_month_estimated": previous_month_estimated,
    }

def build_report_rows(
    most_expensive: List[Tuple[str, List[float]]],
    length: int,
    report_days: int,
    authoritative_total_costs: List[float],
) -> Tuple[List[ReportRow], List[float]]:
    """Build visible service rows while keeping AWS totals authoritative."""
    selected_services = most_expensive[:length]

    visible_services = sorted(
        selected_services,
        key=lambda item: (-len(item[0].strip()), item[0].casefold()),
    )

    rows: List[ReportRow] = []

    for service_name, costs in visible_services:
        rows.append(
            {
                "service": service_name,
                "costs": costs,
                "is_total": False,
            }
        )

    other_costs = [0.0] * report_days

    for _, costs in most_expensive[length:]:
        for index, cost in enumerate(costs):
            other_costs[index] += cost

    rows.append(
        {
            "service": "Other",
            "costs": other_costs,
            "is_total": False,
        }
    )

    total_costs = [float(value) for value in authoritative_total_costs]
    rows.append(
        {
            "service": "Total",
            "costs": total_costs,
            "is_total": True,
        }
    )

    return rows, total_costs

def build_zero_report_data(
    report_days: int,
    report_date: date,
    list_of_dates: List[str],
) -> ReportData:
    zero_costs = [0.0] * report_days

    return {
        "report_days": report_days,
        "report_date": report_date.isoformat(),
        "dates": list_of_dates,
        "rows": [
            {
                "service": "Other",
                "costs": zero_costs.copy(),
                "is_total": False,
            },
            {
                "service": "Total",
                "costs": zero_costs.copy(),
                "is_total": True,
            },
        ],
        "total_costs": zero_costs,
        "total": 0.0,
        "previous_total": 0.0,
        "estimated_by_date": {
            value: False for value in list_of_dates
        },
        "report_estimated": False,
    }

def validate_report_calculations(report_data: ReportData) -> None:
    """Validate service sums against independent AWS daily totals."""
    rows = list(report_data.get("rows", []))
    dates = [str(value) for value in report_data.get("dates", [])]
    total_costs = [
        float(value) for value in report_data.get("total_costs", [])
    ]

    if not rows or not total_costs:
        return

    detail_rows = [
        row for row in rows if not bool(row.get("is_total", False))
    ]

    for day_index, aws_total in enumerate(total_costs):
        services_total = 0.0

        for row in detail_rows:
            costs = [float(value) for value in row.get("costs", [])]
            if day_index < len(costs):
                services_total += costs[day_index]

        difference = services_total - aws_total
        date_label = (
            dates[day_index]
            if day_index < len(dates)
            else f"index {day_index}"
        )

        print(
            "AWS total verification | "
            f"{date_label}: direct={aws_total:.8f}, "
            f"services={services_total:.8f}, "
            f"difference={difference:.8f}"
        )

        if abs(difference) > 0.0001:
            raise RuntimeError(
                "AWS daily total does not match the complete grouped "
                f"service result for {date_label}: direct="
                f"{aws_total:.8f}, services={services_total:.8f}"
            )

    if len(total_costs) < 2:
        return

    previous_date = dates[-2] if len(dates) >= 2 else "previous day"
    current_date = dates[-1] if dates else "current day"

    print(
        "Validated daily comparison: "
        f"{current_date} versus {previous_date}"
    )

    for row in rows:
        service_name = str(row.get("service", "Unknown"))
        costs = [float(value) for value in row.get("costs", [])]

        if len(costs) < 2:
            continue

        previous_cost = costs[-2]
        current_cost = costs[-1]
        percentage = calculate_change_percent(
            previous_cost=previous_cost,
            current_cost=current_cost,
        )

        percentage_text = (
            "NEW" if percentage is None else f"{percentage:+.2f}%"
        )

        print(
            "Calculation check | "
            f"{service_name}: "
            f"{previous_date}={previous_cost:.8f}, "
            f"{current_date}={current_cost:.8f}, "
            f"change={percentage_text}"
        )

def build_console_report(report_data: ReportData) -> str:
    rows = report_data.get("rows", [])
    report_days = int(report_data.get("report_days", DEFAULT_REPORT_DAYS))

    service_names = [str(row.get("service", "Service")) for row in rows]
    longest_name_len = max([len("Service"), *map(len, service_names)])

    lines = [
        (
            f"{'Service':{longest_name_len}} "
            f"{'Yesterday':>12} "
            f"{'Change':>14} "
            f"Last {report_days}d"
        )
    ]

    for row in rows:
        service_name = str(row.get("service", "Unknown"))
        costs = [float(value) for value in row.get("costs", [])]
        current = costs[-1] if costs else 0.0
        trend = sparkline(costs)

        lines.append(
            f"{service_name:{longest_name_len}} "
            f"${current:11,.2f} "
            f"{format_console_change(costs):>14} "
            f"{trend}"
        )

    return "\n".join(lines)


def report_cost(
    session: boto3.Session,
    account_name: str,
    group_by: str = DEFAULT_GROUP_BY,
    length: int = DEFAULT_TOP_SERVICES,
    cost_aggregation: str = DEFAULT_COST_AGGREGATION,
    report_days: int = DEFAULT_REPORT_DAYS,
    end_date_text: Optional[str] = None,
) -> Tuple[str, str, ReportData]:
    """Fetch all displayed daily values from AWS and calculate changes locally."""
    report_days = max(int(report_days), MIN_TREND_DAYS)

    start_date, end_date, report_date = calculate_billing_period(
        report_days=report_days,
        end_date_text=end_date_text,
    )

    list_of_dates = [
        (start_date + timedelta(days=day_number)).isoformat()
        for day_number in range(report_days)
    ]

    print(
        "Daily comparison: "
        f"{list_of_dates[-1]} vs {list_of_dates[-2]}"
    )

    client = session.client("ce", region_name=COST_EXPLORER_REGION)

    daily_totals_by_date, estimated_by_date = get_daily_totals_from_aws(
        client=client,
        start_date=start_date,
        end_date=end_date,
        cost_aggregation=cost_aggregation,
    )
    authoritative_total_costs = [
        daily_totals_by_date.get(billing_date, 0.0)
        for billing_date in list_of_dates
    ]

    grouped_result = get_cost_and_usage_all_pages(
        client=client,
        query={
            "TimePeriod": {
                "Start": start_date.isoformat(),
                "End": end_date.isoformat(),
            },
            "Granularity": "DAILY",
            "Filter": get_cost_filter(),
            "Metrics": [cost_aggregation],
            "GroupBy": [
                {
                    "Type": "DIMENSION",
                    "Key": group_by,
                }
            ],
        },
    )

    print(
        f"Getting complete AWS billing data from "
        f"{start_date.isoformat()} to {end_date.isoformat()} "
        f"for account {account_name}"
    )

    cost_per_day_dict: Dict[str, Dict[str, float]] = defaultdict(dict)
    dimension_attributes = grouped_result.get(
        "DimensionValueAttributes", []
    )

    for day_result in grouped_result.get("ResultsByTime", []):
        result_date = day_result.get("TimePeriod", {}).get("Start")

        if not result_date:
            continue

        for group in day_result.get("Groups", []):
            keys = group.get("Keys", [])

            if not keys:
                continue

            service_name = keys[0]

            if group_by == "LINKED_ACCOUNT":
                dimension = find_by_key(
                    dimension_attributes,
                    "Value",
                    service_name,
                )

                if dimension:
                    description = dimension.get("Attributes", {}).get(
                        "description"
                    )
                    if description:
                        service_name += f" ({description})"

            amount = (
                group.get("Metrics", {})
                .get(cost_aggregation, {})
                .get("Amount", "0")
            )
            cost_per_day_dict[service_name][result_date] = float(amount)

    cost_per_day_by_service: Dict[str, List[float]] = defaultdict(list)

    for service_name, costs_by_date in cost_per_day_dict.items():
        for billing_date in list_of_dates:
            cost_per_day_by_service[service_name].append(
                costs_by_date.get(billing_date, 0.0)
            )

    most_expensive = sorted(
        cost_per_day_by_service.items(),
        key=lambda item: item[1][-1] if item[1] else 0.0,
        reverse=True,
    )

    if not most_expensive and max(authoritative_total_costs, default=0.0) <= 0:
        report_data = build_zero_report_data(
            report_days=report_days,
            report_date=report_date,
            list_of_dates=list_of_dates,
        )
        report_data["estimated_by_date"] = estimated_by_date
        report_data["report_estimated"] = bool(
            estimated_by_date.get(report_date.isoformat(), False)
        )
    elif not most_expensive:
        raise RuntimeError(
            "AWS returned a non-zero daily total but no grouped service "
            "details. The report was not sent to avoid inaccurate data."
        )
    else:
        rows, total_costs = build_report_rows(
            most_expensive=most_expensive,
            length=length,
            report_days=report_days,
            authoritative_total_costs=authoritative_total_costs,
        )

        report_data = {
            "report_days": report_days,
            "report_date": report_date.isoformat(),
            "dates": list_of_dates,
            "rows": rows,
            "total_costs": total_costs,
            "total": total_costs[-1] if total_costs else 0.0,
            "previous_total": (
                total_costs[-2] if len(total_costs) >= 2 else 0.0
            ),
            "estimated_by_date": estimated_by_date,
            "report_estimated": bool(
                estimated_by_date.get(report_date.isoformat(), False)
            ),
        }

    if report_data.get("report_estimated"):
        print(
            "AWS marks the report day as estimated; the value can still "
            "change when AWS finishes processing billing data."
        )
    else:
        print("AWS does not mark the report day as estimated.")

    validate_report_calculations(report_data)
    report_buffer = build_console_report(report_data)
    total_cost = float(report_data.get("total", 0.0))

    summary = build_summary(
        account_name=account_name,
        report_date=report_date,
        total_cost=total_cost,
    )

    return summary, report_buffer, report_data

def build_summary(
    account_name: str,
    report_date: date,
    total_cost: float,
) -> str:
    credits_expire_date_text = os.environ.get("CREDITS_EXPIRE_DATE")

    if not credits_expire_date_text:
        return (
            f"Cost for account {account_name} on {report_date.isoformat()} "
            f"was ${total_cost:,.2f}"
        )

    credits_remaining_as_of_text = get_required_env(
        "CREDITS_REMAINING_AS_OF"
    )
    credits_remaining_text = get_required_env("CREDITS_REMAINING")

    credits_expire_date = datetime.strptime(
        credits_expire_date_text,
        "%m/%d/%Y",
    ).date()

    credits_remaining_as_of = datetime.strptime(
        credits_remaining_as_of_text,
        "%m/%d/%Y",
    ).date()

    credits_remaining = float(credits_remaining_text)
    days_left_on_credits = (
        credits_expire_date - credits_remaining_as_of
    ).days

    if days_left_on_credits <= 0:
        raise ValueError(
            "CREDITS_EXPIRE_DATE must be later than CREDITS_REMAINING_AS_OF"
        )

    allowed_credits_per_day = credits_remaining / days_left_on_credits

    if allowed_credits_per_day <= 0:
        relative_to_budget = 0.0
    else:
        relative_to_budget = (
            total_cost / allowed_credits_per_day
        ) * 100.0

    if relative_to_budget < 60:
        status = "✅"
    elif relative_to_budget > 110:
        status = "🚨"
    else:
        status = "⚠️"

    return (
        f"{status} Cost for account {account_name} on "
        f"{report_date.isoformat()} was ${total_cost:,.2f}. "
        f"This is {relative_to_budget:.2f}% of the daily credit budget "
        f"(${allowed_credits_per_day:,.2f})."
    )


def format_report_date(date_text: str) -> str:
    try:
        parsed_date = datetime.strptime(date_text, "%Y-%m-%d").date()
        return parsed_date.strftime("%d %b %Y")
    except (TypeError, ValueError):
        return str(date_text)


def get_comparison_dates(report_data: ReportData) -> Tuple[str, str]:
    dates = [str(value) for value in report_data.get("dates", [])]

    if len(dates) >= 2:
        return (
            format_report_date(dates[-2]),
            format_report_date(dates[-1]),
        )

    report_date_text = str(report_data.get("report_date", ""))

    if report_date_text:
        try:
            current_date = datetime.strptime(
                report_date_text,
                "%Y-%m-%d",
            ).date()
            previous_date = current_date - timedelta(days=1)
            return (
                previous_date.strftime("%d %b %Y"),
                current_date.strftime("%d %b %Y"),
            )
        except ValueError:
            pass

    return "Previous day", "Report day"

def build_table_row(row: ReportRow) -> Dict[str, Any]:
    service_text = str(row.get("service", "Unknown"))
    costs = [float(value) for value in row.get("costs", [])]
    is_total = bool(row.get("is_total", False))

    current_cost = costs[-1] if costs else 0.0
    previous_cost = costs[-2] if len(costs) >= 2 else 0.0
    change_text, change_color = format_change(previous_cost, current_cost)

    if not costs or max(costs) <= 0:
        chart_color = "Default"
    elif change_color == "Default":
        chart_color = "Accent"
    else:
        chart_color = change_color

    chart_url = chart_data_uri(
        datapoints=costs,
        width=ROW_CHART_WIDTH,
        height=ROW_CHART_HEIGHT,
        color_name=chart_color,
    )

    row_content = {
        "type": "ColumnSet",
        "spacing": "Small",
        "separator": not is_total,
        "columns": [
            {
                "type": "Column",
                "width": 48,
                "items": [
                    {
                        "type": "TextBlock",
                        "text": service_text,
                        "weight": "Bolder" if is_total else "Default",
                        "wrap": True,
                        "maxLines": 2,
                    }
                ],
            },
            {
                "type": "Column",
                "width": 19,
                "items": [
                    {
                        "type": "TextBlock",
                        "text": format_money(current_cost),
                        "weight": "Bolder" if is_total else "Default",
                        "wrap": False,
                    }
                ],
            },
            {
                "type": "Column",
                "width": 18,
                "items": [
                    {
                        "type": "TextBlock",
                        "text": change_text,
                        "color": change_color,
                        "weight": "Bolder",
                        "wrap": False,
                    }
                ],
            },
            {
                "type": "Column",
                "width": 25,
                "items": [
                    {
                        "type": "Image",
                        "url": chart_url,
                        "altText": sparkline(costs),
                        "size": "Stretch",
                        "horizontalAlignment": "Center",
                    }
                ],
            },
        ],
    }

    if is_total:
        return {
            "type": "Container",
            "style": "emphasis",
            "spacing": "Medium",
            "separator": True,
            "items": [row_content],
        }

    return row_content

def build_daily_change_section(report_data: ReportData) -> Dict[str, Any]:
    total_costs = [
        float(value) for value in report_data.get("total_costs", [])
    ]

    current_total = total_costs[-1] if total_costs else 0.0
    previous_total = total_costs[-2] if len(total_costs) >= 2 else 0.0
    difference = round(current_total - previous_total, 2)
    percentage = calculate_change_percent(previous_total, current_total)
    _, change_color = format_change(previous_total, current_total)
    previous_date_label, current_date_label = get_comparison_dates(report_data)

    if difference > 0:
        difference_text = f"+{format_money(difference)}"
        difference_color = "Attention"
        direction_icon = "▲"
    elif difference < 0:
        difference_text = f"−{format_money(abs(difference))}"
        difference_color = "Good"
        direction_icon = "▼"
    else:
        difference_text = format_money(0.0)
        difference_color = "Default"
        direction_icon = "—"

    if percentage is None:
        large_percentage_text = "NEW"
    elif percentage > 0:
        large_percentage_text = f"{direction_icon} {abs(percentage):,.2f}%"
    elif percentage < 0:
        large_percentage_text = f"{direction_icon} {abs(percentage):,.2f}%"
    else:
        large_percentage_text = "— 0.00%"

    chart_color = change_color if change_color != "Default" else "Accent"
    main_chart_url = chart_data_uri(
        datapoints=total_costs,
        width=MAIN_CHART_WIDTH,
        height=MAIN_CHART_HEIGHT,
        color_name=chart_color,
        show_grid=True,
    )

    return {
        "type": "Container",
        "style": "emphasis",
        "spacing": "Large",
        "separator": True,
        "items": [
            {
                "type": "TextBlock",
                "text": "CHANGE FROM PREVIOUS DAY",
                "weight": "Bolder",
                "size": "Medium",
                "wrap": True,
            },
            {
                "type": "ColumnSet",
                "spacing": "Medium",
                "columns": [
                    {
                        "type": "Column",
                        "width": 23,
                        "items": [
                            {
                                "type": "TextBlock",
                                "text": large_percentage_text,
                                "weight": "Bolder",
                                "size": "ExtraLarge",
                                "color": change_color,
                                "wrap": False,
                            }
                        ],
                    },
                    {
                        "type": "Column",
                        "width": 31,
                        "separator": True,
                        "items": [
                            {
                                "type": "FactSet",
                                "facts": [
                                    {
                                        "title": f"{previous_date_label}:",
                                        "value": format_money(previous_total),
                                    },
                                    {
                                        "title": f"{current_date_label}:",
                                        "value": format_money(current_total),
                                    },
                                    {
                                        "title": "Difference:",
                                        "value": difference_text,
                                    },
                                ],
                            }
                        ],
                    },
                    {
                        "type": "Column",
                        "width": 46,
                        "separator": True,
                        "items": [
                            {
                                "type": "Image",
                                "url": main_chart_url,
                                "altText": sparkline(total_costs, width=18),
                                "size": "Stretch",
                                "horizontalAlignment": "Center",
                            }
                        ],
                    },
                ],
            },
        ],
    }

def publish_teams(
    hook_url: str,
    summary: str,
    report_data: ReportData,
    monthly_overview: Dict[str, Any],
) -> None:
    report_days = int(report_data.get("report_days", MIN_TREND_DAYS))
    previous_date_label, current_date_label = get_comparison_dates(report_data)
    table_rows = [
        build_table_row(row)
        for row in report_data.get("rows", [])
    ]

    current_month_cost = float(
        monthly_overview.get("current_month_cost", 0.0)
    )
    forecast_month_end = float(
        monthly_overview.get("forecast_month_end", 0.0)
    )
    current_month_label = str(
        monthly_overview.get("current_month_label", "Current month")
    )
    previous_month_label = str(
        monthly_overview.get("previous_month_label", "previous month")
    )
    forecast_source = str(
        monthly_overview.get(
            "forecast_source",
            "AWS Cost Explorer forecast",
        )
    )

    forecast_change_percent = monthly_overview.get(
        "forecast_change_percent"
    )

    if forecast_change_percent is None:
        monthly_change_text = (
            f"Previous month ({previous_month_label}): US$0.00"
        )
        monthly_change_color = "Default"
    elif forecast_change_percent > 0:
        monthly_change_text = (
            f"▲ {abs(forecast_change_percent):,.0f}% "
            f"vs {previous_month_label}"
        )
        monthly_change_color = "Attention"
    elif forecast_change_percent < 0:
        monthly_change_text = (
            f"▼ {abs(forecast_change_percent):,.0f}% "
            f"vs {previous_month_label}"
        )
        monthly_change_color = "Good"
    else:
        monthly_change_text = f"— 0% vs {previous_month_label}"
        monthly_change_color = "Default"

    payload = {
        "$schema": "http://adaptivecards.io/schemas/adaptive-card.json",
        "type": "AdaptiveCard",
        "version": "1.2",
        "msteams": {"width": "Full"},
        "fallbackText": summary,
        "body": [
            {
                "type": "Container",
                "style": "emphasis",
                "bleed": True,
                "items": [
                    {
                        "type": "TextBlock",
                        "text": "💰 Cost and usage",
                        "weight": "Bolder",
                        "size": "ExtraLarge",
                        "wrap": True,
                    },
                    {
                        "type": "TextBlock",
                        "text": "AWS billing and service usage details",
                        "isSubtle": True,
                        "spacing": "None",
                        "wrap": True,
                    },
                ],
            },
            {
                "type": "ColumnSet",
                "spacing": "Large",
                "columns": [
                    {
                        "type": "Column",
                        "width": "stretch",
                        "items": [
                            {
                                "type": "Container",
                                "style": "accent",
                                "items": [
                                    {
                                        "type": "TextBlock",
                                        "text": "📅  CURRENT MONTH",
                                        "weight": "Bolder",
                                        "size": "Small",
                                        "wrap": True,
                                    },
                                    {
                                        "type": "TextBlock",
                                        "text": format_money(current_month_cost),
                                        "weight": "Bolder",
                                        "size": "ExtraLarge",
                                        "color": "Accent",
                                        "spacing": "Small",
                                        "wrap": True,
                                    },
                                    {
                                        "type": "TextBlock",
                                        "text": current_month_label,
                                        "isSubtle": True,
                                        "spacing": "Small",
                                        "wrap": True,
                                    },
                                ],
                            }
                        ],
                    },
                    {
                        "type": "Column",
                        "width": "stretch",
                        "items": [
                            {
                                "type": "Container",
                                "style": "attention",
                                "items": [
                                    {
                                        "type": "TextBlock",
                                        "text": "📈  FORECAST MONTH END",
                                        "weight": "Bolder",
                                        "size": "Small",
                                        "wrap": True,
                                    },
                                    {
                                        "type": "TextBlock",
                                        "text": format_money(forecast_month_end),
                                        "weight": "Bolder",
                                        "size": "ExtraLarge",
                                        "spacing": "Small",
                                        "wrap": True,
                                    },
                                    {
                                        "type": "TextBlock",
                                        "text": monthly_change_text,
                                        "weight": "Bolder",
                                        "color": monthly_change_color,
                                        "spacing": "Small",
                                        "wrap": True,
                                    },
                                ],
                            }
                        ],
                    },
                ],
            },
            {
                "type": "Container",
                "style": "emphasis",
                "spacing": "Medium",
                "items": [
                    {
                        "type": "FactSet",
                        "facts": [
                            {
                                "title": "Forecast source:",
                                "value": forecast_source,
                            },
                            {
                                "title": "Savings opportunities:",
                                "value": "Not enabled",
                            },
                            {
                                "title": "Daily data status:",
                                "value": (
                                    "Estimated by AWS"
                                    if report_data.get("report_estimated")
                                    else "Not marked estimated by AWS"
                                ),
                            },
                        ],
                    }
                ],
            },
            {
                "type": "TextBlock",
                "text": summary,
                "weight": "Bolder",
                "size": "Medium",
                "spacing": "Medium",
                "wrap": True,
            },
            build_daily_change_section(report_data),
            {
                "type": "TextBlock",
                "text": "Cost details (US$)",
                "weight": "Bolder",
                "size": "Large",
                "spacing": "Large",
                "separator": True,
                "wrap": True,
            },
            {
                "type": "ColumnSet",
                "spacing": "Small",
                "columns": [
                    {
                        "type": "Column",
                        "width": 48,
                        "items": [
                            {
                                "type": "TextBlock",
                                "text": "SERVICE",
                                "weight": "Bolder",
                                "isSubtle": True,
                                "size": "Small",
                                "horizontalAlignment": "Left",
                            }
                        ],
                    },
                    {
                        "type": "Column",
                        "width": 19,
                        "items": [
                            {
                                "type": "TextBlock",
                                "text": f"YESTERDAY\n{current_date_label}",
                                "weight": "Bolder",
                                "isSubtle": True,
                                "size": "Small",
                                "horizontalAlignment": "Left",
                            }
                        ],
                    },
                    {
                        "type": "Column",
                        "width": 18,
                        "items": [
                            {
                                "type": "TextBlock",
                                "text": f"CHANGE\nVS {previous_date_label}",
                                "weight": "Bolder",
                                "isSubtle": True,
                                "size": "Small",
                                "horizontalAlignment": "Left",
                            }
                        ],
                    },
                    {
                        "type": "Column",
                        "width": 25,
                        "items": [
                            {
                                "type": "TextBlock",
                                "text": f"LAST {report_days}D\nTREND",
                                "weight": "Bolder",
                                "isSubtle": True,
                                "size": "Small",
                                "horizontalAlignment": "Left",
                            }
                        ],
                    },
                ],
            },
            *table_rows,
            {
                "type": "Container",
                "spacing": "Medium",
                "separator": True,
                "items": [
                    {
                        "type": "TextBlock",
                        "text": "Generated automatically from AWS Cost Explorer",
                        "isSubtle": True,
                        "size": "Small",
                        "horizontalAlignment": "Right",
                        "wrap": True,
                    }
                ],
            },
        ],
    }

    payload_json = json.dumps(
        payload,
        ensure_ascii=False,
        separators=(",", ":"),
    )
    payload_size = len(payload_json.encode("utf-8"))

    print(f"Teams Adaptive Card payload size: {payload_size} bytes")

    if payload_size > MAX_TEAMS_MESSAGE_BYTES:
        raise RuntimeError(
            "Teams Adaptive Card is larger than the supported 28 KB limit: "
            f"{payload_size} bytes"
        )

    try:
        response = requests.post(
            hook_url,
            data=payload_json.encode("utf-8"),
            headers={"Content-Type": "application/json; charset=utf-8"},
            timeout=HTTP_TIMEOUT_SECONDS,
        )

        print(
            f"Teams webhook response: {response.status_code} - {response.text}"
        )
        response.raise_for_status()
    except requests.RequestException as error:
        raise RuntimeError(
            f"Failed to send notification to Microsoft Teams: {error}"
        ) from error

def run() -> None:
    group_by = os.environ.get(
        "GROUP_BY",
        DEFAULT_GROUP_BY,
    ).strip()

    length = get_positive_int_env("LENGTH", DEFAULT_TOP_SERVICES)
    report_days = max(
        get_positive_int_env(
            "REPORT_DAYS",
            DEFAULT_REPORT_DAYS,
        ),
        MIN_TREND_DAYS,
    )

    cost_aggregation = os.environ.get(
        "COST_AGGREGATION",
        DEFAULT_COST_AGGREGATION,
    ).strip()

    billing_end_date_raw = os.environ.get("BILLING_END_DATE", "").strip()
    billing_end_date = billing_end_date_raw or None

    if billing_end_date:
        print(
            "BILLING_END_DATE is set, so the report date is fixed at "
            f"{billing_end_date}. Remove this variable for automatic "
            "day-by-day reporting."
        )
    teams_hook_url = get_required_env("TEAMS_WEBHOOK_URL")
    accounts = load_aws_accounts()
    failed_accounts: List[str] = []

    for account in accounts:
        account_name = str(account["name"])

        try:
            print(f"Processing AWS account: {account_name}")
            session = create_aws_session(account)
            verify_aws_identity(
                session=session,
                account_name=account_name,
                expected_account_id=account.get("expected_account_id"),
            )

            monthly_overview = get_monthly_cost_overview(
                session=session,
                cost_aggregation=cost_aggregation,
                end_date_text=billing_end_date,
            )

            summary, report_buffer, report_data = report_cost(
                session=session,
                account_name=account_name,
                group_by=group_by,
                length=length,
                cost_aggregation=cost_aggregation,
                report_days=report_days,
                end_date_text=billing_end_date,
            )

            print(summary)
            print(report_buffer)

            publish_teams(
                hook_url=teams_hook_url,
                summary=summary,
                report_data=report_data,
                monthly_overview=monthly_overview,
            )

            print(f"Teams notification sent for account: {account_name}")

        except ClientError as error:
            error_code = error.response.get("Error", {}).get("Code", "")

            if error_code == "DataUnavailableException":
                start_date, _, report_date = calculate_billing_period(
                    report_days=report_days,
                    end_date_text=billing_end_date,
                )

                list_of_dates = [
                    (start_date + timedelta(days=day_number)).isoformat()
                    for day_number in range(report_days)
                ]

                report_data = build_zero_report_data(
                    report_days=report_days,
                    report_date=report_date,
                    list_of_dates=list_of_dates,
                )
                report_buffer = build_console_report(report_data)

                summary = build_summary(
                    account_name=account_name,
                    report_date=report_date,
                    total_cost=0.0,
                )

                print(summary)
                print(report_buffer)

                monthly_overview = get_monthly_cost_overview(
                    session=session,
                    cost_aggregation=cost_aggregation,
                    end_date_text=billing_end_date,
                )

                publish_teams(
                    hook_url=teams_hook_url,
                    summary=summary,
                    report_data=report_data,
                    monthly_overview=monthly_overview,
                )

                print(f"Teams notification sent for account: {account_name}")
            else:
                print(
                    f"Failed to process account {account_name}: {error}",
                    file=sys.stderr,
                )
                failed_accounts.append(account_name)

        except (
            BotoCoreError,
            NoCredentialsError,
            requests.RequestException,
            RuntimeError,
            ValueError,
        ) as error:
            print(
                f"Failed to process account {account_name}: {error}",
                file=sys.stderr,
            )
            failed_accounts.append(account_name)

    if failed_accounts:
        raise RuntimeError(
            "Failed AWS accounts: " + ", ".join(failed_accounts)
        )


def lambda_handler(
    event: Any = None,
    context: Any = None,
) -> Dict[str, Any]:
    run()

    return {
        "statusCode": 200,
        "body": "AWS billing reports were processed successfully.",
    }


if __name__ == "__main__":
    try:
        run()
    except Exception as error:
        print(f"Application failed: {error}", file=sys.stderr)
        sys.exit(1)