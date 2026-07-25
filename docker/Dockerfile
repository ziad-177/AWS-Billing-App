FROM python:3.10-slim

WORKDIR /app

RUN pip install --no-cache-dir pipenv

COPY scripts/aws-billing/Pipfile ./
COPY scripts/aws-billing/Pipfile.lock ./

RUN pipenv install --system --deploy --ignore-pipfile

COPY scripts/aws-billing/handler.py ./

CMD ["python", "handler.py"]