from __future__ import annotations

import base64
import binascii
import hashlib
import html
import json
import logging
import os
import re
import sqlite3
import time
import unicodedata
import xml.etree.ElementTree as ET
from collections import Counter
from datetime import UTC, datetime, timedelta
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen
from zoneinfo import ZoneInfo

from flask import Flask, abort, g, jsonify, request, send_from_directory, session
from werkzeug.security import check_password_hash, generate_password_hash

ROOT = Path(__file__).resolve().parent.parent


def load_env_file(path: Path) -> None:
    if not path.exists():
        return
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip().strip('"').strip("'")
        if key and key not in os.environ:
            os.environ[key] = value


load_env_file(ROOT / ".env")

DATA_PATH = ROOT / "backend" / "worldcup-2026.json"
QUIZ_PATH = ROOT / "backend" / "quiz-2026.json"
TEAM_PROFILES_PATH = ROOT / "backend" / "team-profiles-2026.json"
DB_PATH = Path(os.environ.get("WK_HUB_SQLITE_PATH", ROOT / "backend" / "pool.db"))
DB_SCHEMA_VERSION = 4
PROFILE_IMAGE_MAX_BYTES = 750 * 1024
PROFILE_IMAGE_DATA_URL_PATTERN = re.compile(
    r"^data:image/(png|jpeg|jpg|webp|gif);base64,([A-Za-z0-9+/=\s]+)$"
)
PASSWORD_MIN_LENGTH = 8
DEFAULT_PASSWORD = "default-password"
DB_BACKUP_TABLES: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("users", ("id",)),
    ("match_predictions", ("user_id", "match_id")),
    ("winner_predictions", ("user_id",)),
    ("top_scorer_predictions", ("user_id",)),
    ("quiz_predictions", ("user_id", "match_id")),
    ("leeuwtje_predictions", ("user_id", "match_id")),
    ("user_follows", ("follower_id", "followed_id")),
    ("prediction_audit_log", ("id",)),
    ("api_football_team_links", ("local_team_id",)),
    ("api_football_fixture_links", ("match_id",)),
    ("api_football_requests", ("id",)),
    ("api_football_fixture_snapshots", ("match_id",)),
    ("api_football_fixture_snapshot_history", ("id",)),
    ("api_football_team_squad_snapshots", ("local_team_id",)),
    ("api_football_team_squad_snapshot_history", ("id",)),
    ("team_squad_players", ("local_team_id", "provider_player_key")),
    ("team_coaches", ("local_team_id", "provider_coach_key")),
    ("match_results", ("match_id",)),
    ("match_events", ("match_id", "provider_event_key")),
    ("match_clean_sheets", ("match_id", "local_team_id")),
    ("player_match_stats", ("match_id", "provider_player_key")),
    ("newsletter_articles", ("published_at", "url")),
)
DIST_DIR = ROOT / "frontend" / "dist"
DATABASE_URL_ENV = "DATABASE_URL" if os.environ.get("DATABASE_URL") else None
if DATABASE_URL_ENV is None and os.environ.get("POSTGRES_URL"):
    DATABASE_URL_ENV = "POSTGRES_URL"
DATABASE_URL = os.environ.get("DATABASE_URL") or os.environ.get("POSTGRES_URL")
SCHEMA_DATABASE_URL_ENV = (
    "DATABASE_URL_UNPOOLED" if os.environ.get("DATABASE_URL_UNPOOLED") else DATABASE_URL_ENV
)
SCHEMA_DATABASE_URL = os.environ.get("DATABASE_URL_UNPOOLED") or DATABASE_URL
USING_POSTGRES = bool(DATABASE_URL)
IS_VERCEL = os.environ.get("VERCEL") == "1"
CONFIG_ERROR = (
    "Set DATABASE_URL from Neon, or POSTGRES_URL, for Talpa WK Pool on Vercel."
    if IS_VERCEL and not DATABASE_URL
    else None
)
LOG_LEVEL_NAME = os.environ.get("WK_HUB_LOG_LEVEL", "INFO").upper()
LOG_LEVEL = getattr(logging, LOG_LEVEL_NAME, logging.INFO)
if not isinstance(LOG_LEVEL, int):
    LOG_LEVEL = logging.INFO
PREDICTION_LOCK_BEFORE_KICKOFF = timedelta(hours=1)
# Matches separated by less than this gap belong to the same playing session.
# World Cup 2026 matches are often played overnight (Dutch time): the early-hours
# kickoffs of the next calendar day are part of the same matchday for NL viewers.
# Overnight gaps are ~6-8h; the daytime gap to the next evening session is much
# larger, so this threshold cleanly separates one matchday from the next.
MATCHDAY_SESSION_GAP = timedelta(hours=12)
NETHERLANDS_TEAM_ID = "ned"
AMSTERDAM_TZ = ZoneInfo("Europe/Amsterdam")
LEEUWTJES_LIMIT = 5
GROUP_POSITION_POINTS = 25
WINNER_POINTS = 250
TOP_SCORER_POINTS = 100
STRIKER_PICK_COUNT = 5
STRIKER_GOAL_POINTS = 10
QUIZ_YES_NO_POINTS = 15
QUIZ_OPEN_POINTS = 12
QUIZ_VIEWERSHIP_POINTS = 15
API_FOOTBALL_BASE_URL = os.environ.get(
    "API_FOOTBALL_BASE_URL", "https://v3.football.api-sports.io"
).rstrip("/")
API_FOOTBALL_KEY = os.environ.get("API_FOOTBALL_KEY", "")
API_FOOTBALL_LEAGUE_ID = int(os.environ.get("API_FOOTBALL_LEAGUE_ID", "1"))
API_FOOTBALL_SEASON = int(os.environ.get("API_FOOTBALL_SEASON", "2026"))
API_FOOTBALL_DAILY_LIMIT = int(os.environ.get("API_FOOTBALL_DAILY_LIMIT", "90"))
API_FOOTBALL_SQUAD_SYNC_BATCH_SIZE = int(
    os.environ.get("API_FOOTBALL_SQUAD_SYNC_BATCH_SIZE", "6")
)
API_FOOTBALL_SQUAD_REFRESH_HOURS = int(
    os.environ.get("API_FOOTBALL_SQUAD_REFRESH_HOURS", "24")
)
API_FOOTBALL_SYNC_TOKEN = os.environ.get("WK_HUB_SYNC_TOKEN") or os.environ.get(
    "CRON_SECRET", ""
)
API_FOOTBALL_POSTMATCH_BUFFER = timedelta(
    minutes=int(os.environ.get("API_FOOTBALL_POSTMATCH_BUFFER_MINUTES", "135"))
)
API_FOOTBALL_FINAL_RESYNC_AFTER = timedelta(
    hours=int(os.environ.get("API_FOOTBALL_FINAL_RESYNC_HOURS", "12"))
)
API_FOOTBALL_FINAL_STATUSES = {"FT", "AET", "PEN"}
API_FOOTBALL_MAX_BATCH_SIZE = 20
NEWSLETTER_MAX_ARTICLES = int(os.environ.get("NEWSLETTER_MAX_ARTICLES", "6"))
NEWSLETTER_FEEDS: tuple[dict[str, str], ...] = (
    {
        "name": "Google News NL",
        "country": "Netherlands",
        "url": (
            "https://news.google.com/rss/search?"
            "q=WK%202026%20voetbal%20OR%20Wereldkampioenschap%202026%20voetbal"
            "&hl=nl&gl=NL&ceid=NL:nl"
        ),
    },
    {
        "name": "Google News BE",
        "country": "Belgium",
        "url": (
            "https://news.google.com/rss/search?"
            "q=WK%202026%20voetbal%20OR%20Rode%20Duivels%20WK%202026"
            "&hl=nl&gl=BE&ceid=BE:nl"
        ),
    },
)
MATCH_SCORE_RULES = {
    "Group Stage": {"exact": 45, "outcome": 30},
    "Round of 32": {"exact": 90, "outcome": 60},
    "Round of 16": {"exact": 135, "outcome": 90},
    "Quarter-final": {"exact": 180, "outcome": 120},
    "Semi-final": {"exact": 225, "outcome": 150},
    "Third-place play-off": {"exact": 225, "outcome": 150},
    "Final": {"exact": 270, "outcome": 180},
}

logging.basicConfig(
    level=LOG_LEVEL,
    format="%(asctime)s %(levelname)s [%(name)s] %(message)s",
)
logger = logging.getLogger("wk_hub")
if CONFIG_ERROR:
    logger.error(CONFIG_ERROR)


def database_label() -> str:
    if CONFIG_ERROR:
        return "unconfigured database"
    if USING_POSTGRES:
        return f"postgres:{DATABASE_URL_ENV or 'unknown env'}"
    return f"sqlite:{DB_PATH}"


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as file:
        for chunk in iter(lambda: file.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def json_ready(value: Any) -> Any:
    if isinstance(value, datetime):
        return iso_utc(value.astimezone(UTC)) if value.tzinfo else value.isoformat()
    if isinstance(value, sqlite3.Row):
        keys = value.keys()
        return {key: json_ready(value[key]) for key in keys}
    if isinstance(value, dict):
        return {str(key): json_ready(item) for key, item in value.items()}
    if isinstance(value, list | tuple):
        return [json_ready(item) for item in value]
    return value


def static_data_manifest() -> dict[str, Any]:
    return {
        "worldcup_path": str(DATA_PATH.relative_to(ROOT)),
        "worldcup_sha256": file_sha256(DATA_PATH),
        "quiz_path": str(QUIZ_PATH.relative_to(ROOT)) if QUIZ_PATH.exists() else None,
        "quiz_sha256": file_sha256(QUIZ_PATH),
        "team_profiles_path": (
            str(TEAM_PROFILES_PATH.relative_to(ROOT)) if TEAM_PROFILES_PATH.exists() else None
        ),
        "team_profiles_sha256": file_sha256(TEAM_PROFILES_PATH),
    }


def load_world_cup_data() -> dict[str, Any]:
    with DATA_PATH.open(encoding="utf-8") as data_file:
        data = json.load(data_file)

    if QUIZ_PATH.exists():
        with QUIZ_PATH.open(encoding="utf-8") as quiz_file:
            quiz_data = json.load(quiz_file)
        quizzes = quiz_data.get("matches", {})
        for match in data["matches"]:
            quiz = quizzes.get(match["id"])
            if quiz:
                match["quiz"] = quiz
        data.setdefault("meta", {})["quiz_answer_source"] = quiz_data.get("answerSource")

    apply_static_team_profiles(data)

    if not CONFIG_ERROR:
        apply_synced_team_profiles(data)
        apply_synced_match_results(data)

    return data


def merge_team_profile(team: dict[str, Any], profile: dict[str, Any]) -> None:
    current = dict(team.get("profile") or team.get("team_profile") or {})
    for key, value in profile.items():
        if key == "sources":
            current_sources = list_value(current.get("sources"))
            for source in list_value(value):
                if source not in current_sources:
                    current_sources.append(source)
            if current_sources:
                current["sources"] = current_sources
        elif value not in (None, "", []):
            current[key] = value
    if current:
        team["profile"] = current


def apply_static_team_profiles(data: dict[str, Any]) -> None:
    if not TEAM_PROFILES_PATH.exists():
        return
    try:
        with TEAM_PROFILES_PATH.open(encoding="utf-8") as profiles_file:
            profiles_data = json.load(profiles_file)
    except Exception:
        logger.exception("Could not load static team profiles")
        return

    by_team = {
        team.get("id"): team
        for team in profiles_data.get("teams", [])
        if isinstance(team, dict) and team.get("id")
    }
    source = profiles_data.get("source") or {}
    for team in data.get("teams", []):
        profile = by_team.get(team.get("id"))
        if not profile:
            continue
        profile_payload: dict[str, Any] = {}
        if profile.get("squad"):
            profile_payload["squad"] = profile["squad"]
        if profile.get("head_coach"):
            profile_payload["head_coach"] = profile["head_coach"]
            profile_payload["coaching_staff"] = [profile["head_coach"]]
        if source:
            profile_payload["sources"] = [source]
        merge_team_profile(team, profile_payload)


def utc_now() -> datetime:
    return datetime.now(UTC)


def match_kickoff(match: dict[str, Any]) -> datetime:
    return datetime.fromisoformat(f"{match['date']}T{match['time_utc']}:00+00:00")


def match_lock_time(match: dict[str, Any]) -> datetime:
    return match_kickoff(match) - PREDICTION_LOCK_BEFORE_KICKOFF


def is_prediction_locked(match: dict[str, Any], now: datetime | None = None) -> bool:
    if match.get("status") != "scheduled":
        return True
    return (now or utc_now()) >= match_lock_time(match)


def winner_lock_time(data: dict[str, Any]) -> datetime:
    group_matches = [match for match in data["matches"] if match["round"] == "Group Stage"]
    first_match = min(group_matches, key=match_kickoff)
    return match_lock_time(first_match)


def is_winner_locked(data: dict[str, Any], now: datetime | None = None) -> bool:
    return (now or utc_now()) >= winner_lock_time(data)


def iso_utc(value: datetime) -> str:
    return value.isoformat().replace("+00:00", "Z")


def parse_iso_datetime(value: Any) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(str(value).replace("Z", "+00:00"))
    except ValueError:
        return None


app = Flask(__name__, static_folder=None)
app.secret_key = os.environ.get("WK_HUB_SECRET", "wk-hub-local-dev-secret")
logger.info("Starting Talpa WK Pool backend with %s", database_label())


@app.before_request
def track_request_start() -> None:
    g.request_start_time = time.perf_counter()


@app.before_request
def reject_misconfigured_deployment() -> Any | None:
    if CONFIG_ERROR and request.path.startswith("/api/") and request.path != "/api/health":
        return jsonify({"ok": False, "error": CONFIG_ERROR}), 503
    return None


@app.after_request
def log_request(response: Any) -> Any:
    duration_ms = (
        time.perf_counter() - getattr(g, "request_start_time", time.perf_counter())
    ) * 1000
    logger.info(
        "%s %s -> %s %.1fms", request.method, request.path, response.status_code, duration_ms
    )
    return response


def bind(query: str) -> str:
    if USING_POSTGRES:
        return query.replace("?", "%s")
    return query


def execute(conn: Any, query: str, params: tuple[Any, ...] = ()) -> Any:
    return conn.execute(bind(query), params)


def get_db(*, schema: bool = False) -> Any:
    if USING_POSTGRES:
        import psycopg
        from psycopg.rows import dict_row

        conninfo = SCHEMA_DATABASE_URL if schema else DATABASE_URL
        assert conninfo is not None
        return psycopg.connect(conninfo, row_factory=dict_row)

    if IS_VERCEL:
        raise RuntimeError(CONFIG_ERROR or "Vercel deployments must use Postgres.")

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def database_snapshot(*, include_rows: bool) -> dict[str, Any]:
    tables: dict[str, Any] = {}
    with get_db() as conn:
        for table_name, order_by in DB_BACKUP_TABLES:
            row = execute(conn, f"SELECT COUNT(*) AS count FROM {table_name}").fetchone()
            table_payload: dict[str, Any] = {"count": int(row["count"] if row else 0)}
            if include_rows:
                order_clause = ", ".join(order_by)
                rows = execute(
                    conn, f"SELECT * FROM {table_name} ORDER BY {order_clause}"
                ).fetchall()
                table_payload["rows"] = [json_ready(row) for row in rows]
            tables[table_name] = table_payload

    return {
        "ok": True,
        "generated_at": iso_utc(utc_now()),
        "schema_version": DB_SCHEMA_VERSION,
        "database": database_label(),
        "static_data": static_data_manifest(),
        "tables": tables,
    }


def strip_html(value: Any) -> str:
    text = re.sub(r"<[^>]+>", " ", str(value or ""))
    return clean_text(html.unescape(text))


def parse_rss_datetime(value: str) -> str | None:
    text = clean_text(value)
    if not text:
        return None
    from email.utils import parsedate_to_datetime

    try:
        parsed = parsedate_to_datetime(text)
    except (TypeError, ValueError):
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=UTC)
    return iso_utc(parsed.astimezone(UTC))


def fetch_newsletter_feed(feed: dict[str, str]) -> list[dict[str, Any]]:
    request_obj = Request(
        feed["url"],
        headers={
            "User-Agent": "wk-hub/1.0 (+https://wk-hub.local)",
        },
    )
    with urlopen(request_obj, timeout=12) as response:
        payload = response.read(2_000_000)
    root = ET.fromstring(payload)
    articles = []
    for item in root.findall(".//item"):
        title = clean_text(item.findtext("title"))
        url = clean_text(item.findtext("link"))
        if not title or not url:
            continue
        source_node = item.find("source")
        publisher = (
            clean_text(source_node.text if source_node is not None else "")
            or feed["name"]
        )
        articles.append(
            {
                "title": title,
                "publisher": publisher,
                "country": feed["country"],
                "summary": strip_html(item.findtext("description"))[:320],
                "url": url,
                "source": feed["name"],
                "published_at": parse_rss_datetime(item.findtext("pubDate") or ""),
            }
        )
    return articles


def newsletter_articles_from_db(limit: int = NEWSLETTER_MAX_ARTICLES) -> list[dict[str, Any]]:
    with get_db() as conn:
        rows = execute(
            conn,
            """
            SELECT title, publisher, country, summary, url, source, published_at, refreshed_at
            FROM newsletter_articles
            ORDER BY published_at DESC NULLS LAST, refreshed_at DESC, title
            LIMIT ?
            """,
            (limit,),
        ).fetchall()
    return [json_ready(row) for row in rows]


def fallback_newsletter_articles() -> list[dict[str, Any]]:
    return [
        {
            "title": "WK 2026 levert landen recordbedrag op",
            "publisher": "NU.nl",
            "country": "Netherlands",
            "summary": (
                "FIFA raises the prize pool for the 2026 World Cup, with a larger base "
                "payout for every qualified country."
            ),
            "url": (
                "https://www.nu.nl/voetbal/6379805/"
                "wk-2026-levert-landen-recordbedrag-op-wereldkampioen-krijgt-42-miljoen-euro.html"
            ),
            "source": "Static fallback",
            "published_at": None,
            "refreshed_at": None,
        },
        {
            "title": "FIFA WK voetbal 2026 en 2030 live bij de NOS",
            "publisher": "NOS",
            "country": "Netherlands",
            "summary": "NOS outlines its broadcast role for the 2026 and 2030 men's World Cups.",
            "url": "https://over.nos.nl/nieuws/fifa-wk-voetbal-2026-en-2030-live-bij-de-nos/",
            "source": "Static fallback",
            "published_at": None,
            "refreshed_at": None,
        },
        {
            "title": "Het volledige speelschema van de Rode Duivels",
            "publisher": "VoetbalPrimeur.be",
            "country": "Belgium",
            "summary": (
                "Belgian coverage of the Red Devils' group-stage schedule, opponents and "
                "kick-off windows."
            ),
            "url": (
                "https://www.voetbalprimeur.be/nieuws/1718992/"
                "wk-voetbal-2026-ontdek-hier-het-volledige-speelschema-van-de-rode-duivels.html"
            ),
            "source": "Static fallback",
            "published_at": None,
            "refreshed_at": None,
        },
    ]


def newsletter_articles(limit: int = NEWSLETTER_MAX_ARTICLES) -> list[dict[str, Any]]:
    articles = newsletter_articles_from_db(limit)
    return articles if articles else fallback_newsletter_articles()[:limit]


def run_newsletter_refresh() -> dict[str, Any]:
    fetched: list[dict[str, Any]] = []
    errors = []
    seen_urls = set()
    for feed in NEWSLETTER_FEEDS:
        try:
            articles = fetch_newsletter_feed(feed)
        except (ET.ParseError, HTTPError, TimeoutError, URLError, OSError) as error:
            logger.warning("Newsletter feed refresh failed for %s: %s", feed["name"], error)
            errors.append({"source": feed["name"], "error": str(error)})
            continue
        for article in articles:
            if article["url"] in seen_urls:
                continue
            seen_urls.add(article["url"])
            fetched.append(article)

    fetched = sorted(
        fetched,
        key=lambda article: article.get("published_at") or "",
        reverse=True,
    )[:NEWSLETTER_MAX_ARTICLES]
    if fetched:
        with get_db() as conn:
            for article in fetched:
                execute(
                    conn,
                    """
                    INSERT INTO newsletter_articles (
                        url, title, publisher, country, summary, source, published_at, refreshed_at
                    )
                    VALUES (?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                    ON CONFLICT(url)
                    DO UPDATE SET title = excluded.title,
                                  publisher = excluded.publisher,
                                  country = excluded.country,
                                  summary = excluded.summary,
                                  source = excluded.source,
                                  published_at = excluded.published_at,
                                  refreshed_at = CURRENT_TIMESTAMP
                    """,
                    (
                        article["url"],
                        article["title"],
                        article.get("publisher"),
                        article.get("country"),
                        article.get("summary"),
                        article["source"],
                        article.get("published_at"),
                    ),
                )
            conn.commit()

    return {
        "ok": bool(fetched) or not errors,
        "fetched": len(fetched),
        "errors": errors,
        "articles": fetched,
    }


def init_db() -> None:
    sqlite_schema = [
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            email TEXT NOT NULL UNIQUE,
            profile_image_url TEXT,
            password_hash TEXT,
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS match_predictions (
            user_id INTEGER NOT NULL,
            match_id TEXT NOT NULL,
            home_score INTEGER NOT NULL,
            away_score INTEGER NOT NULL,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, match_id),
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS winner_predictions (
            user_id INTEGER PRIMARY KEY,
            team_id TEXT NOT NULL,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS top_scorer_predictions (
            user_id INTEGER PRIMARY KEY,
            player_name TEXT NOT NULL,
            player_name_2 TEXT,
            player_name_3 TEXT,
            striker_name_1 TEXT,
            striker_name_2 TEXT,
            striker_name_3 TEXT,
            striker_name_4 TEXT,
            striker_name_5 TEXT,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS quiz_predictions (
            user_id INTEGER NOT NULL,
            match_id TEXT NOT NULL,
            answer TEXT,
            viewership_prediction INTEGER,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, match_id),
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS leeuwtje_predictions (
            user_id INTEGER NOT NULL,
            match_id TEXT NOT NULL,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, match_id),
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS user_follows (
            follower_id INTEGER NOT NULL,
            followed_id INTEGER NOT NULL,
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (follower_id, followed_id),
            FOREIGN KEY (follower_id) REFERENCES users(id),
            FOREIGN KEY (followed_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS prediction_audit_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            action TEXT NOT NULL,
            payload_json TEXT NOT NULL,
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_team_links (
            local_team_id TEXT PRIMARY KEY,
            api_team_id INTEGER NOT NULL UNIQUE,
            api_team_name TEXT,
            confidence TEXT NOT NULL,
            linked_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_fixture_links (
            match_id TEXT PRIMARY KEY,
            api_fixture_id INTEGER NOT NULL UNIQUE,
            api_home_team_id INTEGER,
            api_away_team_id INTEGER,
            api_home_team_name TEXT,
            api_away_team_name TEXT,
            confidence TEXT NOT NULL,
            linked_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_requests (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            requested_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            endpoint TEXT NOT NULL,
            params_json TEXT NOT NULL,
            status_code INTEGER,
            ok INTEGER NOT NULL,
            error TEXT
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_fixture_snapshots (
            match_id TEXT PRIMARY KEY,
            api_fixture_id INTEGER NOT NULL,
            payload_json TEXT NOT NULL,
            synced_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_fixture_snapshot_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            match_id TEXT NOT NULL,
            api_fixture_id INTEGER NOT NULL,
            payload_json TEXT NOT NULL,
            synced_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_team_squad_snapshots (
            local_team_id TEXT PRIMARY KEY,
            api_team_id INTEGER NOT NULL,
            squad_payload_json TEXT NOT NULL,
            coach_payload_json TEXT,
            synced_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_team_squad_snapshot_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            local_team_id TEXT NOT NULL,
            api_team_id INTEGER NOT NULL,
            squad_payload_json TEXT NOT NULL,
            coach_payload_json TEXT,
            synced_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS team_squad_players (
            local_team_id TEXT NOT NULL,
            provider_player_key TEXT NOT NULL,
            source_team_id INTEGER,
            api_player_id INTEGER,
            player_name TEXT NOT NULL,
            age INTEGER,
            number INTEGER,
            position TEXT,
            photo_url TEXT,
            raw_json TEXT NOT NULL,
            synced_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (local_team_id, provider_player_key)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS team_coaches (
            local_team_id TEXT NOT NULL,
            provider_coach_key TEXT NOT NULL,
            source_team_id INTEGER,
            api_coach_id INTEGER,
            coach_name TEXT NOT NULL,
            age INTEGER,
            nationality TEXT,
            photo_url TEXT,
            raw_json TEXT NOT NULL,
            synced_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (local_team_id, provider_coach_key)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS match_results (
            match_id TEXT PRIMARY KEY,
            source TEXT NOT NULL,
            source_fixture_id INTEGER,
            status_long TEXT,
            status_short TEXT,
            elapsed INTEGER,
            home_score INTEGER,
            away_score INTEGER,
            synced_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS match_events (
            match_id TEXT NOT NULL,
            provider_event_key TEXT NOT NULL,
            source_fixture_id INTEGER,
            elapsed INTEGER,
            extra INTEGER,
            local_team_id TEXT,
            api_team_id INTEGER,
            team_name TEXT,
            api_player_id INTEGER,
            player_name TEXT,
            api_assist_id INTEGER,
            assist_name TEXT,
            event_type TEXT NOT NULL,
            detail TEXT,
            comments TEXT,
            raw_json TEXT NOT NULL,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (match_id, provider_event_key)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS match_clean_sheets (
            match_id TEXT NOT NULL,
            local_team_id TEXT NOT NULL,
            api_team_id INTEGER,
            team_name TEXT,
            source_fixture_id INTEGER,
            synced_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (match_id, local_team_id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS player_match_stats (
            match_id TEXT NOT NULL,
            provider_player_key TEXT NOT NULL,
            source_fixture_id INTEGER,
            local_team_id TEXT,
            api_team_id INTEGER,
            team_name TEXT,
            api_player_id INTEGER,
            player_name TEXT NOT NULL,
            minutes INTEGER,
            position TEXT,
            rating TEXT,
            goals INTEGER NOT NULL DEFAULT 0,
            assists INTEGER NOT NULL DEFAULT 0,
            yellow_cards INTEGER NOT NULL DEFAULT 0,
            red_cards INTEGER NOT NULL DEFAULT 0,
            clean_sheet INTEGER NOT NULL DEFAULT 0,
            raw_json TEXT NOT NULL,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (match_id, provider_player_key)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS newsletter_articles (
            url TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            publisher TEXT,
            country TEXT,
            summary TEXT,
            source TEXT NOT NULL,
            published_at TEXT,
            refreshed_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
    ]
    postgres_schema = [
        """
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
            name TEXT NOT NULL,
            email TEXT NOT NULL UNIQUE,
            profile_image_url TEXT,
            password_hash TEXT,
            created_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS match_predictions (
            user_id INTEGER NOT NULL,
            match_id TEXT NOT NULL,
            home_score INTEGER NOT NULL,
            away_score INTEGER NOT NULL,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, match_id),
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS winner_predictions (
            user_id INTEGER PRIMARY KEY,
            team_id TEXT NOT NULL,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS top_scorer_predictions (
            user_id INTEGER PRIMARY KEY,
            player_name TEXT NOT NULL,
            player_name_2 TEXT,
            player_name_3 TEXT,
            striker_name_1 TEXT,
            striker_name_2 TEXT,
            striker_name_3 TEXT,
            striker_name_4 TEXT,
            striker_name_5 TEXT,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS quiz_predictions (
            user_id INTEGER NOT NULL,
            match_id TEXT NOT NULL,
            answer TEXT,
            viewership_prediction INTEGER,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, match_id),
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS leeuwtje_predictions (
            user_id INTEGER NOT NULL,
            match_id TEXT NOT NULL,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, match_id),
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS user_follows (
            follower_id INTEGER NOT NULL,
            followed_id INTEGER NOT NULL,
            created_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (follower_id, followed_id),
            FOREIGN KEY (follower_id) REFERENCES users(id),
            FOREIGN KEY (followed_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS prediction_audit_log (
            id INTEGER GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
            user_id INTEGER,
            action TEXT NOT NULL,
            payload_json TEXT NOT NULL,
            created_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY (user_id) REFERENCES users(id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_team_links (
            local_team_id TEXT PRIMARY KEY,
            api_team_id INTEGER NOT NULL UNIQUE,
            api_team_name TEXT,
            confidence TEXT NOT NULL,
            linked_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_fixture_links (
            match_id TEXT PRIMARY KEY,
            api_fixture_id INTEGER NOT NULL UNIQUE,
            api_home_team_id INTEGER,
            api_away_team_id INTEGER,
            api_home_team_name TEXT,
            api_away_team_name TEXT,
            confidence TEXT NOT NULL,
            linked_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_requests (
            id INTEGER GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
            requested_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            endpoint TEXT NOT NULL,
            params_json TEXT NOT NULL,
            status_code INTEGER,
            ok INTEGER NOT NULL,
            error TEXT
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_fixture_snapshots (
            match_id TEXT PRIMARY KEY,
            api_fixture_id INTEGER NOT NULL,
            payload_json TEXT NOT NULL,
            synced_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_fixture_snapshot_history (
            id INTEGER GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
            match_id TEXT NOT NULL,
            api_fixture_id INTEGER NOT NULL,
            payload_json TEXT NOT NULL,
            synced_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_team_squad_snapshots (
            local_team_id TEXT PRIMARY KEY,
            api_team_id INTEGER NOT NULL,
            squad_payload_json TEXT NOT NULL,
            coach_payload_json TEXT,
            synced_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS api_football_team_squad_snapshot_history (
            id INTEGER GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
            local_team_id TEXT NOT NULL,
            api_team_id INTEGER NOT NULL,
            squad_payload_json TEXT NOT NULL,
            coach_payload_json TEXT,
            synced_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS team_squad_players (
            local_team_id TEXT NOT NULL,
            provider_player_key TEXT NOT NULL,
            source_team_id INTEGER,
            api_player_id INTEGER,
            player_name TEXT NOT NULL,
            age INTEGER,
            number INTEGER,
            position TEXT,
            photo_url TEXT,
            raw_json TEXT NOT NULL,
            synced_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (local_team_id, provider_player_key)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS team_coaches (
            local_team_id TEXT NOT NULL,
            provider_coach_key TEXT NOT NULL,
            source_team_id INTEGER,
            api_coach_id INTEGER,
            coach_name TEXT NOT NULL,
            age INTEGER,
            nationality TEXT,
            photo_url TEXT,
            raw_json TEXT NOT NULL,
            synced_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (local_team_id, provider_coach_key)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS match_results (
            match_id TEXT PRIMARY KEY,
            source TEXT NOT NULL,
            source_fixture_id INTEGER,
            status_long TEXT,
            status_short TEXT,
            elapsed INTEGER,
            home_score INTEGER,
            away_score INTEGER,
            synced_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS match_events (
            match_id TEXT NOT NULL,
            provider_event_key TEXT NOT NULL,
            source_fixture_id INTEGER,
            elapsed INTEGER,
            extra INTEGER,
            local_team_id TEXT,
            api_team_id INTEGER,
            team_name TEXT,
            api_player_id INTEGER,
            player_name TEXT,
            api_assist_id INTEGER,
            assist_name TEXT,
            event_type TEXT NOT NULL,
            detail TEXT,
            comments TEXT,
            raw_json TEXT NOT NULL,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (match_id, provider_event_key)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS match_clean_sheets (
            match_id TEXT NOT NULL,
            local_team_id TEXT NOT NULL,
            api_team_id INTEGER,
            team_name TEXT,
            source_fixture_id INTEGER,
            synced_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (match_id, local_team_id)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS player_match_stats (
            match_id TEXT NOT NULL,
            provider_player_key TEXT NOT NULL,
            source_fixture_id INTEGER,
            local_team_id TEXT,
            api_team_id INTEGER,
            team_name TEXT,
            api_player_id INTEGER,
            player_name TEXT NOT NULL,
            minutes INTEGER,
            position TEXT,
            rating TEXT,
            goals INTEGER NOT NULL DEFAULT 0,
            assists INTEGER NOT NULL DEFAULT 0,
            yellow_cards INTEGER NOT NULL DEFAULT 0,
            red_cards INTEGER NOT NULL DEFAULT 0,
            clean_sheet INTEGER NOT NULL DEFAULT 0,
            raw_json TEXT NOT NULL,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (match_id, provider_player_key)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS newsletter_articles (
            url TEXT PRIMARY KEY,
            title TEXT NOT NULL,
            publisher TEXT,
            country TEXT,
            summary TEXT,
            source TEXT NOT NULL,
            published_at TIMESTAMPTZ,
            refreshed_at TIMESTAMPTZ NOT NULL DEFAULT CURRENT_TIMESTAMP
        )
        """,
    ]

    with get_db(schema=True) as conn:
        if USING_POSTGRES:
            for statement in postgres_schema:
                conn.execute(statement)
            quiz_viewership_column = conn.execute(
                """
                SELECT 1
                FROM information_schema.columns
                WHERE table_name = 'quiz_predictions'
                  AND column_name = 'viewership_prediction'
                """
            ).fetchone()
            if quiz_viewership_column is None:
                conn.execute(
                    "ALTER TABLE quiz_predictions ADD COLUMN viewership_prediction INTEGER"
                )
            user_profile_image_column = conn.execute(
                """
                SELECT 1
                FROM information_schema.columns
                WHERE table_name = 'users'
                  AND column_name = 'profile_image_url'
                """
            ).fetchone()
            if user_profile_image_column is None:
                conn.execute("ALTER TABLE users ADD COLUMN profile_image_url TEXT")
            user_password_column = conn.execute(
                """
                SELECT 1
                FROM information_schema.columns
                WHERE table_name = 'users'
                  AND column_name = 'password_hash'
                """
            ).fetchone()
            if user_password_column is None:
                conn.execute("ALTER TABLE users ADD COLUMN password_hash TEXT")
            execute(
                conn,
                """
                UPDATE users
                SET password_hash = ?
                WHERE password_hash IS NULL OR password_hash = ''
                """,
                (generate_password_hash(DEFAULT_PASSWORD),),
            )
            top_scorer_columns_to_add = (
                "player_name_2",
                "player_name_3",
                "striker_name_1",
                "striker_name_2",
                "striker_name_3",
                "striker_name_4",
                "striker_name_5",
            )
            for column_name in top_scorer_columns_to_add:
                top_scorer_column = conn.execute(
                    """
                    SELECT 1
                    FROM information_schema.columns
                    WHERE table_name = 'top_scorer_predictions'
                      AND column_name = %s
                    """,
                    (column_name,),
                ).fetchone()
                if top_scorer_column is None:
                    conn.execute(
                        f"ALTER TABLE top_scorer_predictions ADD COLUMN {column_name} TEXT"
                    )
        else:
            conn.executescript(";\n".join(sqlite_schema))
            quiz_columns = conn.execute("PRAGMA table_info(quiz_predictions)").fetchall()
            if not any(row["name"] == "viewership_prediction" for row in quiz_columns):
                conn.execute(
                    "ALTER TABLE quiz_predictions ADD COLUMN viewership_prediction INTEGER"
                )
            user_columns = conn.execute("PRAGMA table_info(users)").fetchall()
            if not any(row["name"] == "profile_image_url" for row in user_columns):
                conn.execute("ALTER TABLE users ADD COLUMN profile_image_url TEXT")
            if not any(row["name"] == "password_hash" for row in user_columns):
                conn.execute("ALTER TABLE users ADD COLUMN password_hash TEXT")
            execute(
                conn,
                """
                UPDATE users
                SET password_hash = ?
                WHERE password_hash IS NULL OR password_hash = ''
                """,
                (generate_password_hash(DEFAULT_PASSWORD),),
            )
            top_scorer_columns = conn.execute(
                "PRAGMA table_info(top_scorer_predictions)"
            ).fetchall()
            top_scorer_column_names = {row["name"] for row in top_scorer_columns}
            top_scorer_columns_to_add = (
                "player_name_2",
                "player_name_3",
                "striker_name_1",
                "striker_name_2",
                "striker_name_3",
                "striker_name_4",
                "striker_name_5",
            )
            for column_name in top_scorer_columns_to_add:
                if column_name not in top_scorer_column_names:
                    conn.execute(
                        f"ALTER TABLE top_scorer_predictions ADD COLUMN {column_name} TEXT"
                    )
    logger.info("Database schema ready using %s", SCHEMA_DATABASE_URL_ENV or database_label())


def row_to_user(row: Any) -> dict[str, Any] | None:
    if row is None:
        return None
    return {
        "id": row["id"],
        "name": row["name"],
        "email": row["email"],
        "profile_picture": user_profile_picture(row),
    }


def current_user() -> dict[str, Any] | None:
    user_id = session.get("user_id")
    if not user_id:
        return None
    with get_db() as conn:
        row = execute(
            conn,
            "SELECT id, name, email, profile_image_url FROM users WHERE id = ?",
            (user_id,),
        ).fetchone()
    return row_to_user(row)


def match_result(match: dict[str, Any]) -> int | None:
    home = match.get("home_score")
    away = match.get("away_score")
    if not isinstance(home, int) or not isinstance(away, int):
        return None
    return (home > away) - (home < away)


def prediction_result(prediction: Any) -> int:
    return (prediction["home_score"] > prediction["away_score"]) - (
        prediction["home_score"] < prediction["away_score"]
    )


def clean_text(value: Any) -> str:
    return " ".join(str(value or "").strip().split())


def row_value(row: Any, key: str, default: Any = None) -> Any:
    try:
        return row[key]
    except (KeyError, IndexError):
        return default


def user_profile_picture(user: Any) -> dict[str, Any]:
    name = row_value(user, "name", "Unknown") if user is not None else "Unknown"
    image_url = row_value(user, "profile_image_url")
    picture = {
        "initials": initials(name),
        "hue": avatar_hue(name),
    }
    if image_url:
        picture["image_url"] = image_url
    return picture


def validate_profile_image_url(value: Any) -> str | None:
    if value in (None, ""):
        return None
    if not isinstance(value, str):
        raise ValueError("Profile image must be an image upload.")
    match = PROFILE_IMAGE_DATA_URL_PATTERN.match(value.strip())
    if not match:
        raise ValueError("Use a PNG, JPG, WebP or GIF image.")
    try:
        decoded = base64.b64decode(match.group(2), validate=True)
    except (binascii.Error, ValueError) as error:
        raise ValueError("The uploaded image could not be read.") from error
    if len(decoded) > PROFILE_IMAGE_MAX_BYTES:
        raise ValueError("Profile image must be smaller than 750 KB.")
    return value.strip()


def validate_password(value: Any) -> str:
    password = str(value or "")
    if len(password) < PASSWORD_MIN_LENGTH:
        raise ValueError(f"Password must be at least {PASSWORD_MIN_LENGTH} characters.")
    if len(password) > 256:
        raise ValueError("Password must be at most 256 characters.")
    return password


def normalize_identity(value: Any) -> str:
    return clean_text(value).casefold()


def normalize_email(value: Any) -> str:
    return str(value or "").strip().casefold()


def normalize_answer(value: Any) -> str:
    return clean_text(value).casefold()


def top_scorer_result_name(data: dict[str, Any]) -> str:
    meta = data.get("meta", {})
    for key in (
        "world_cup_top_scorer_name",
        "top_scorer_name",
        "golden_boot_winner_name",
    ):
        value = clean_text(meta.get(key))
        if value:
            return value
    top_scorer = meta.get("world_cup_top_scorer") or meta.get("top_scorer")
    if isinstance(top_scorer, dict):
        return clean_text(top_scorer.get("name"))
    return clean_text(top_scorer)


def eliminated_team_ids(data: dict[str, Any]) -> set[str]:
    meta = data.get("meta", {})
    values = (
        meta.get("eliminated_team_ids")
        or meta.get("eliminated_teams")
        or meta.get("knocked_out_team_ids")
        or []
    )
    if not isinstance(values, list):
        return set()
    eliminated = set()
    for value in values:
        if isinstance(value, dict):
            team_id = clean_text(value.get("id") or value.get("team_id"))
        else:
            team_id = clean_text(value)
        if team_id:
            eliminated.add(team_id)
    return eliminated


def normalized_player_name(value: Any) -> str:
    return compact_name(value)


STRIKER_COLUMN_NAMES = tuple(f"striker_name_{index}" for index in range(1, STRIKER_PICK_COUNT + 1))


def row_has_key(row: Any, key: str) -> bool:
    try:
        row[key]
    except (KeyError, IndexError):
        return False
    return True


def top_scorer_pick_name(row: Any | None) -> str:
    if not row:
        return ""
    return clean_text(row["player_name"] if row_has_key(row, "player_name") else None)


def striker_pick_names(row: Any | None) -> list[str]:
    if not row:
        return []
    names = [
        name
        for name in [
            clean_text(row[column] if row_has_key(row, column) else None)
            for column in STRIKER_COLUMN_NAMES
        ]
        if name
    ]
    if names:
        return names
    return [
        name
        for name in (
            clean_text(row["player_name"] if row_has_key(row, "player_name") else None),
            clean_text(row["player_name_2"] if row_has_key(row, "player_name_2") else None),
            clean_text(row["player_name_3"] if row_has_key(row, "player_name_3") else None),
        )
        if name
    ]


def striker_pick_rows(row: Any | None) -> list[dict[str, Any]]:
    return [
        {"rank": rank, "name": name, "points_per_goal": STRIKER_GOAL_POINTS}
        for rank, name in enumerate(striker_pick_names(row), start=1)
    ]


def striker_pick_score_rows(
    row: Any | None,
    goal_counts: Counter[str] | None = None,
) -> list[dict[str, Any]]:
    counts = goal_counts if goal_counts is not None else goal_counts_by_player()
    scored_rows = []
    for pick in striker_pick_rows(row):
        goals = counts[normalized_player_name(pick["name"])]
        scored_rows.append(
            {
                **pick,
                "goals": goals,
                "points": goals * STRIKER_GOAL_POINTS,
            }
        )
    return scored_rows


def goal_counts_by_player() -> Counter[str]:
    with get_db() as conn:
        rows = execute(
            conn,
            """
            SELECT player_name, event_type, detail, comments
            FROM match_events
            WHERE LOWER(event_type) = 'goal'
            """,
        ).fetchall()
    counts: Counter[str] = Counter()
    for row in rows:
        detail = normalize_answer(row["detail"])
        comments = normalize_answer(row["comments"])
        if "own goal" in detail or "own goal" in comments:
            continue
        player_name = normalized_player_name(row["player_name"])
        if player_name:
            counts[player_name] += 1
    return counts


def top_scorer_prediction_points(
    data: dict[str, Any],
    player_name: str | None,
) -> int:
    result_name = top_scorer_result_name(data)
    if result_name and normalize_answer(result_name) == normalize_answer(player_name):
        return TOP_SCORER_POINTS
    return 0


def striker_prediction_points(
    picks: list[str],
    goal_counts: Counter[str] | None = None,
) -> int:
    counts = goal_counts if goal_counts is not None else goal_counts_by_player()
    return sum(
        counts[normalized_player_name(player_name)] * STRIKER_GOAL_POINTS
        for player_name in picks
    )


def normalize_api_name(value: Any) -> str:
    normalized = unicodedata.normalize("NFKD", str(value or ""))
    ascii_text = normalized.encode("ascii", "ignore").decode("ascii")
    return "".join(char.casefold() if char.isalnum() else " " for char in ascii_text)


def compact_name(value: Any) -> str:
    return " ".join(normalize_api_name(value).split())


API_FOOTBALL_TEAM_ALIASES = {
    "bosnia herz egovina": "bih",
    "bosnia and herzegovina": "bih",
    "cape verde": "cpv",
    "congo dr": "cod",
    "curacao": "cuw",
    "czech republic": "cze",
    "czechia": "cze",
    "dr congo": "cod",
    "england": "eng",
    "ha ti": "hai",
    "ivory coast": "civ",
    "korea republic": "kor",
    "netherlands": "ned",
    "paraguay": "par",
    "republic of korea": "kor",
    "scotland": "sco",
    "south korea": "kor",
    "turkey": "tur",
    "turkiye": "tur",
    "united states": "usa",
    "united states of america": "usa",
    "usa": "usa",
}


def local_team_id_from_name(name: Any, data: dict[str, Any]) -> str | None:
    normalized = compact_name(name)
    if normalized in API_FOOTBALL_TEAM_ALIASES:
        return API_FOOTBALL_TEAM_ALIASES[normalized]

    by_name = {compact_name(team["name"]): team["id"] for team in data["teams"]}
    by_code = {compact_name(team["code"]): team["id"] for team in data["teams"]}
    return by_name.get(normalized) or by_code.get(normalized)


def int_or_none(value: Any) -> int | None:
    if value is None or value == "":
        return None
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def bool_int(value: bool) -> int:
    return 1 if value else 0


def list_value(value: Any) -> list[Any]:
    if not value:
        return []
    if isinstance(value, list):
        return list(value)
    return [value]


def api_football_request_count_today() -> int:
    today_start = datetime.now(UTC).replace(hour=0, minute=0, second=0, microsecond=0)
    with get_db() as conn:
        row = execute(
            conn,
            """
            SELECT COUNT(*) AS count
            FROM api_football_requests
            WHERE requested_at >= ?
            """,
            (today_start,),
        ).fetchone()
    return int(row["count"] if row else 0)


def record_api_football_request(
    endpoint: str,
    params: dict[str, Any],
    status_code: int | None,
    ok: bool,
    error: str | None = None,
) -> None:
    with get_db() as conn:
        execute(
            conn,
            """
            INSERT INTO api_football_requests (
                endpoint, params_json, status_code, ok, error, requested_at
            )
            VALUES (?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
            """,
            (
                endpoint,
                json.dumps(params, sort_keys=True),
                status_code,
                bool_int(ok),
                error,
            ),
        )


def api_football_get(endpoint: str, params: dict[str, Any]) -> dict[str, Any]:
    if not API_FOOTBALL_KEY:
        raise RuntimeError("API_FOOTBALL_KEY is not configured.")
    if api_football_request_count_today() >= API_FOOTBALL_DAILY_LIMIT:
        raise RuntimeError(
            f"API-Football daily request limit reached ({API_FOOTBALL_DAILY_LIMIT})."
        )

    query = urlencode({key: value for key, value in params.items() if value is not None})
    url = f"{API_FOOTBALL_BASE_URL}/{endpoint.lstrip('/')}"
    if query:
        url = f"{url}?{query}"
    request_obj = Request(url, headers={"x-apisports-key": API_FOOTBALL_KEY})

    status_code = None
    try:
        with urlopen(request_obj, timeout=20) as response:
            status_code = response.status
            payload = json.loads(response.read().decode("utf-8"))
        record_api_football_request(endpoint, params, status_code, True)
        errors = payload.get("errors")
        if errors:
            raise RuntimeError(f"API-Football returned errors: {errors}")
        return payload
    except HTTPError as error:
        status_code = error.code
        body = error.read().decode("utf-8", errors="replace")
        record_api_football_request(endpoint, params, status_code, False, body[:500])
        raise RuntimeError(f"API-Football HTTP {status_code}: {body[:160]}") from error
    except (URLError, TimeoutError) as error:
        record_api_football_request(endpoint, params, status_code, False, str(error)[:500])
        raise RuntimeError(f"API-Football request failed: {error}") from error


def api_football_status() -> dict[str, Any]:
    with get_db() as conn:
        team_linked_row = execute(
            conn, "SELECT COUNT(*) AS count FROM api_football_team_links"
        ).fetchone()
        linked_row = execute(
            conn, "SELECT COUNT(*) AS count FROM api_football_fixture_links"
        ).fetchone()
        result_row = execute(conn, "SELECT COUNT(*) AS count FROM match_results").fetchone()
        squad_row = execute(
            conn, "SELECT COUNT(*) AS count FROM api_football_team_squad_snapshots"
        ).fetchone()
        player_row = execute(conn, "SELECT COUNT(*) AS count FROM team_squad_players").fetchone()
        coach_row = execute(conn, "SELECT COUNT(*) AS count FROM team_coaches").fetchone()
        latest_request = execute(
            conn,
            """
            SELECT requested_at, endpoint, status_code, ok, error
            FROM api_football_requests
            ORDER BY requested_at DESC
            LIMIT 1
            """,
        ).fetchone()

    return {
        "configured": bool(API_FOOTBALL_KEY),
        "protected": bool(API_FOOTBALL_SYNC_TOKEN),
        "league": API_FOOTBALL_LEAGUE_ID,
        "season": API_FOOTBALL_SEASON,
        "daily_limit": API_FOOTBALL_DAILY_LIMIT,
        "requests_today": api_football_request_count_today(),
        "linked_teams": int(team_linked_row["count"] if team_linked_row else 0),
        "linked_matches": int(linked_row["count"] if linked_row else 0),
        "synced_results": int(result_row["count"] if result_row else 0),
        "synced_squads": int(squad_row["count"] if squad_row else 0),
        "squad_players": int(player_row["count"] if player_row else 0),
        "coaches": int(coach_row["count"] if coach_row else 0),
        "latest_request": dict(latest_request) if latest_request else None,
    }


def apply_synced_match_results(data: dict[str, Any]) -> None:
    try:
        with get_db() as conn:
            rows = execute(
                conn,
                """
                SELECT match_id, source_fixture_id, status_long, status_short, elapsed,
                       home_score, away_score, synced_at
                FROM match_results
                """,
            ).fetchall()
    except Exception:
        logger.exception("Could not load synced match results")
        return

    by_match = {row["match_id"]: row for row in rows}
    for match in data.get("matches", []):
        row = by_match.get(match["id"])
        if not row:
            continue
        match["api_football"] = {
            "fixture_id": row["source_fixture_id"],
            "status": row["status_short"],
            "synced_at": row["synced_at"],
        }
        if (
            row["status_short"] in API_FOOTBALL_FINAL_STATUSES
            and row["home_score"] is not None
            and row["away_score"] is not None
        ):
            match["status"] = "completed"
            match["home_score"] = int(row["home_score"])
            match["away_score"] = int(row["away_score"])


def apply_synced_team_profiles(data: dict[str, Any]) -> None:
    try:
        with get_db() as conn:
            player_rows = execute(
                conn,
                """
                SELECT local_team_id, api_player_id, player_name, age, number,
                       position, photo_url, synced_at
                FROM team_squad_players
                ORDER BY local_team_id, position, number, player_name
                """,
            ).fetchall()
            coach_rows = execute(
                conn,
                """
                SELECT local_team_id, api_coach_id, coach_name, age, nationality,
                       photo_url, synced_at
                FROM team_coaches
                ORDER BY local_team_id, coach_name
                """,
            ).fetchall()
            snapshot_rows = execute(
                conn,
                """
                SELECT local_team_id, api_team_id, synced_at
                FROM api_football_team_squad_snapshots
                """,
            ).fetchall()
    except Exception:
        logger.exception("Could not load synced team profiles")
        return

    players_by_team: dict[str, list[dict[str, Any]]] = {}
    for row in player_rows:
        player = {
            "id": row["api_player_id"],
            "name": row["player_name"],
            "age": row["age"],
            "number": row["number"],
            "position": row["position"],
            "photo": row["photo_url"],
        }
        players_by_team.setdefault(row["local_team_id"], []).append(
            {key: value for key, value in player.items() if value is not None}
        )

    coaches_by_team: dict[str, list[dict[str, Any]]] = {}
    for row in coach_rows:
        coach = {
            "id": row["api_coach_id"],
            "name": row["coach_name"],
            "role": "Head coach",
            "age": row["age"],
            "country": row["nationality"],
            "photo": row["photo_url"],
        }
        coaches_by_team.setdefault(row["local_team_id"], []).append(
            {key: value for key, value in coach.items() if value is not None}
        )

    snapshots_by_team = {row["local_team_id"]: row for row in snapshot_rows}
    for team in data.get("teams", []):
        local_team_id = team.get("id")
        if not local_team_id:
            continue
        players = players_by_team.get(local_team_id)
        coaches = coaches_by_team.get(local_team_id)
        snapshot = snapshots_by_team.get(local_team_id)
        if not players and not coaches and not snapshot:
            continue

        profile = dict(team.get("profile") or team.get("team_profile") or {})
        if players:
            profile["squad"] = players
        if coaches:
            profile["head_coach"] = coaches[0]
            profile["coaching_staff"] = coaches
        if snapshot:
            profile["api_football"] = {
                "team_id": snapshot["api_team_id"],
                "synced_at": snapshot["synced_at"],
            }
            sources = list_value(profile.get("sources"))
            if not any(
                isinstance(source, dict)
                and source.get("label") == "API-Football squad sync"
                for source in sources
            ):
                sources.append({"label": "API-Football squad sync"})
            profile["sources"] = sources
        team["profile"] = profile


def api_fixture_datetime(api_fixture: dict[str, Any]) -> datetime | None:
    return parse_iso_datetime(api_fixture.get("fixture", {}).get("date"))


def provider_team_mapping(
    match: dict[str, Any], fixture: dict[str, Any], data: dict[str, Any]
) -> dict[int, str]:
    teams = fixture.get("teams", {})
    mapping: dict[int, str] = {}
    for side in ("home", "away"):
        api_team = teams.get(side) or {}
        api_team_id = int_or_none(api_team.get("id"))
        local_team_id = local_team_id_from_name(api_team.get("name"), data)
        if api_team_id is not None and local_team_id:
            mapping[api_team_id] = local_team_id

    if not mapping:
        home_id = int_or_none((teams.get("home") or {}).get("id"))
        away_id = int_or_none((teams.get("away") or {}).get("id"))
        if home_id is not None:
            mapping[home_id] = match["home_team_id"]
        if away_id is not None:
            mapping[away_id] = match["away_team_id"]
    return mapping


def local_score_from_fixture(
    match: dict[str, Any], fixture: dict[str, Any], data: dict[str, Any]
) -> tuple[int | None, int | None]:
    goals = fixture.get("goals") or {}
    api_home_score = int_or_none(goals.get("home"))
    api_away_score = int_or_none(goals.get("away"))
    if api_home_score is None or api_away_score is None:
        return None, None

    mapping = provider_team_mapping(match, fixture, data)
    api_home_id = int_or_none((fixture.get("teams", {}).get("home") or {}).get("id"))
    api_away_id = int_or_none((fixture.get("teams", {}).get("away") or {}).get("id"))
    api_home_local = mapping.get(api_home_id) if api_home_id is not None else None
    api_away_local = mapping.get(api_away_id) if api_away_id is not None else None

    if api_home_local == match["home_team_id"] and api_away_local == match["away_team_id"]:
        return api_home_score, api_away_score
    if api_home_local == match["away_team_id"] and api_away_local == match["home_team_id"]:
        return api_away_score, api_home_score
    return api_home_score, api_away_score


def team_conceded_by_local_id(
    match: dict[str, Any],
    fixture: dict[str, Any],
    data: dict[str, Any],
) -> dict[str, int]:
    home_score, away_score = local_score_from_fixture(match, fixture, data)
    if home_score is None or away_score is None:
        return {}
    return {
        match["home_team_id"]: away_score,
        match["away_team_id"]: home_score,
    }


def upsert_api_football_team_link(
    conn: Any,
    local_team_id: str | None,
    api_team_id: int | None,
    api_team_name: str | None,
    confidence: str,
) -> None:
    if not local_team_id or api_team_id is None:
        return
    execute(
        conn,
        """
        INSERT INTO api_football_team_links (
            local_team_id, api_team_id, api_team_name, confidence, linked_at
        )
        VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
        ON CONFLICT(local_team_id)
        DO UPDATE SET api_team_id = excluded.api_team_id,
                      api_team_name = excluded.api_team_name,
                      confidence = excluded.confidence,
                      linked_at = CURRENT_TIMESTAMP
        """,
        (local_team_id, api_team_id, api_team_name, confidence),
    )


def api_football_link_fixtures(data: dict[str, Any]) -> dict[str, Any]:
    payload = api_football_get(
        "fixtures",
        {"league": API_FOOTBALL_LEAGUE_ID, "season": API_FOOTBALL_SEASON},
    )
    fixtures = payload.get("response", [])
    matches_by_pair: dict[frozenset[str], list[dict[str, Any]]] = {}
    for match in data["matches"]:
        pair = frozenset([match["home_team_id"], match["away_team_id"]])
        matches_by_pair.setdefault(pair, []).append(match)

    linked = 0
    skipped = 0
    with get_db() as conn:
        for fixture in fixtures:
            teams = fixture.get("teams", {})
            home_team = teams.get("home") or {}
            away_team = teams.get("away") or {}
            home_local = local_team_id_from_name(home_team.get("name"), data)
            away_local = local_team_id_from_name(away_team.get("name"), data)
            api_fixture_id = int_or_none((fixture.get("fixture") or {}).get("id"))
            if not home_local or not away_local or api_fixture_id is None:
                skipped += 1
                continue

            candidates = matches_by_pair.get(frozenset([home_local, away_local]), [])
            if not candidates:
                skipped += 1
                continue
            fixture_date = api_fixture_datetime(fixture)
            if fixture_date:
                match = min(
                    candidates,
                    key=lambda candidate: abs(
                        (match_kickoff(candidate) - fixture_date).total_seconds()
                    ),
                )
                delta_seconds = abs((match_kickoff(match) - fixture_date).total_seconds())
                if delta_seconds > 36 * 60 * 60:
                    skipped += 1
                    continue
                confidence = "team_pair_and_kickoff"
            else:
                match = candidates[0]
                confidence = "team_pair"

            execute(
                conn,
                """
                INSERT INTO api_football_fixture_links (
                    match_id, api_fixture_id, api_home_team_id, api_away_team_id,
                    api_home_team_name, api_away_team_name, confidence, linked_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                ON CONFLICT(match_id)
                DO UPDATE SET api_fixture_id = excluded.api_fixture_id,
                              api_home_team_id = excluded.api_home_team_id,
                              api_away_team_id = excluded.api_away_team_id,
                              api_home_team_name = excluded.api_home_team_name,
                              api_away_team_name = excluded.api_away_team_name,
                              confidence = excluded.confidence,
                              linked_at = CURRENT_TIMESTAMP
                """,
                (
                    match["id"],
                    api_fixture_id,
                    int_or_none(home_team.get("id")),
                    int_or_none(away_team.get("id")),
                    home_team.get("name"),
                    away_team.get("name"),
                    confidence,
                ),
            )
            upsert_api_football_team_link(
                conn,
                home_local,
                int_or_none(home_team.get("id")),
                home_team.get("name"),
                confidence,
            )
            upsert_api_football_team_link(
                conn,
                away_local,
                int_or_none(away_team.get("id")),
                away_team.get("name"),
                confidence,
            )
            linked += 1

    return {"linked": linked, "skipped": skipped, "fixtures_seen": len(fixtures)}


def api_football_fixture_links() -> dict[str, int]:
    with get_db() as conn:
        rows = execute(
            conn,
            "SELECT match_id, api_fixture_id FROM api_football_fixture_links",
        ).fetchall()
    return {row["match_id"]: int(row["api_fixture_id"]) for row in rows}


def synced_result_rows() -> dict[str, Any]:
    with get_db() as conn:
        rows = execute(
            conn,
            """
            SELECT match_id, status_short, synced_at
            FROM match_results
            """,
        ).fetchall()
    return {row["match_id"]: row for row in rows}


def due_api_football_matches(
    data: dict[str, Any],
    force: bool = False,
    limit: int = API_FOOTBALL_MAX_BATCH_SIZE,
) -> list[dict[str, Any]]:
    current = utc_now()
    synced = synced_result_rows()
    due = []
    for match in sorted(data["matches"], key=match_kickoff):
        if not match.get("home_team_id") or not match.get("away_team_id"):
            continue
        if not force and current < match_kickoff(match) + API_FOOTBALL_POSTMATCH_BUFFER:
            continue
        row = synced.get(match["id"])
        if row and row["status_short"] in API_FOOTBALL_FINAL_STATUSES and not force:
            synced_at = parse_iso_datetime(row["synced_at"])
            if synced_at and current < synced_at + API_FOOTBALL_FINAL_RESYNC_AFTER:
                continue
        due.append(match)
        if len(due) >= limit:
            break
    return due


def event_key(event: dict[str, Any], index: int) -> str:
    time_data = event.get("time") or {}
    team = event.get("team") or {}
    player = event.get("player") or {}
    assist = event.get("assist") or {}
    parts = [
        time_data.get("elapsed"),
        time_data.get("extra"),
        team.get("id"),
        player.get("id") or player.get("name"),
        assist.get("id") or assist.get("name"),
        event.get("type"),
        event.get("detail"),
        event.get("comments"),
        index,
    ]
    return "|".join(str(part or "") for part in parts)


def store_api_football_fixture_snapshot(
    conn: Any,
    match: dict[str, Any],
    fixture: dict[str, Any],
    data: dict[str, Any],
) -> dict[str, Any]:
    api_fixture = fixture.get("fixture") or {}
    api_fixture_id = int_or_none(api_fixture.get("id"))
    if api_fixture_id is None:
        raise ValueError(f"API-Football fixture for {match['id']} has no fixture id.")

    status = api_fixture.get("status") or {}
    status_short = status.get("short")
    home_score, away_score = local_score_from_fixture(match, fixture, data)
    elapsed = int_or_none(status.get("elapsed"))
    mapping = provider_team_mapping(match, fixture, data)
    conceded = team_conceded_by_local_id(match, fixture, data)
    final = status_short in API_FOOTBALL_FINAL_STATUSES

    execute(
        conn,
        """
        INSERT INTO api_football_fixture_snapshots (
            match_id, api_fixture_id, payload_json, synced_at
        )
        VALUES (?, ?, ?, CURRENT_TIMESTAMP)
        ON CONFLICT(match_id)
        DO UPDATE SET api_fixture_id = excluded.api_fixture_id,
                      payload_json = excluded.payload_json,
                      synced_at = CURRENT_TIMESTAMP
        """,
        (match["id"], api_fixture_id, json.dumps(fixture, sort_keys=True)),
    )
    execute(
        conn,
        """
        INSERT INTO api_football_fixture_snapshot_history (
            match_id, api_fixture_id, payload_json, synced_at
        )
        VALUES (?, ?, ?, CURRENT_TIMESTAMP)
        """,
        (match["id"], api_fixture_id, json.dumps(fixture, sort_keys=True)),
    )
    execute(
        conn,
        """
        INSERT INTO match_results (
            match_id, source, source_fixture_id, status_long, status_short,
            elapsed, home_score, away_score, synced_at
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
        ON CONFLICT(match_id)
        DO UPDATE SET source = excluded.source,
                      source_fixture_id = excluded.source_fixture_id,
                      status_long = excluded.status_long,
                      status_short = excluded.status_short,
                      elapsed = excluded.elapsed,
                      home_score = excluded.home_score,
                      away_score = excluded.away_score,
                      synced_at = CURRENT_TIMESTAMP
        """,
        (
            match["id"],
            "api-football",
            api_fixture_id,
            status.get("long"),
            status_short,
            elapsed,
            home_score,
            away_score,
        ),
    )

    execute(conn, "DELETE FROM match_events WHERE match_id = ?", (match["id"],))
    for index, event in enumerate(fixture.get("events") or []):
        team = event.get("team") or {}
        player = event.get("player") or {}
        assist = event.get("assist") or {}
        api_team_id = int_or_none(team.get("id"))
        time_data = event.get("time") or {}
        execute(
            conn,
            """
            INSERT INTO match_events (
                match_id, provider_event_key, source_fixture_id, elapsed, extra,
                local_team_id, api_team_id, team_name, api_player_id, player_name,
                api_assist_id, assist_name, event_type, detail, comments, raw_json,
                updated_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
            """,
            (
                match["id"],
                event_key(event, index),
                api_fixture_id,
                int_or_none(time_data.get("elapsed")),
                int_or_none(time_data.get("extra")),
                mapping.get(api_team_id) if api_team_id is not None else None,
                api_team_id,
                team.get("name"),
                int_or_none(player.get("id")),
                player.get("name"),
                int_or_none(assist.get("id")),
                assist.get("name"),
                event.get("type") or "",
                event.get("detail"),
                event.get("comments"),
                json.dumps(event, sort_keys=True),
            ),
        )

    execute(conn, "DELETE FROM match_clean_sheets WHERE match_id = ?", (match["id"],))
    if final:
        clean_sheet_api_ids = {
            api_team_id
            for api_team_id, local_team_id in mapping.items()
            if conceded.get(local_team_id) == 0
        }
        teams = fixture.get("teams") or {}
        for side in ("home", "away"):
            api_team = teams.get(side) or {}
            api_team_id = int_or_none(api_team.get("id"))
            if api_team_id is None or api_team_id not in clean_sheet_api_ids:
                continue
            local_team_id = mapping.get(api_team_id)
            if not local_team_id:
                continue
            execute(
                conn,
                """
                INSERT INTO match_clean_sheets (
                    match_id, local_team_id, api_team_id, team_name, source_fixture_id, synced_at
                )
                VALUES (?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                ON CONFLICT(match_id, local_team_id)
                DO UPDATE SET api_team_id = excluded.api_team_id,
                              team_name = excluded.team_name,
                              source_fixture_id = excluded.source_fixture_id,
                              synced_at = CURRENT_TIMESTAMP
                """,
                (match["id"], local_team_id, api_team_id, api_team.get("name"), api_fixture_id),
            )

    execute(conn, "DELETE FROM player_match_stats WHERE match_id = ?", (match["id"],))
    for team_block in fixture.get("players") or []:
        api_team = team_block.get("team") or {}
        api_team_id = int_or_none(api_team.get("id"))
        local_team_id = mapping.get(api_team_id) if api_team_id is not None else None
        team_clean_sheet = bool(final and local_team_id and conceded.get(local_team_id) == 0)
        for player_block in team_block.get("players") or []:
            player = player_block.get("player") or {}
            statistics = (player_block.get("statistics") or [{}])[0] or {}
            games = statistics.get("games") or {}
            goals = statistics.get("goals") or {}
            cards = statistics.get("cards") or {}
            api_player_id = int_or_none(player.get("id"))
            player_name = player.get("name") or "Unknown"
            provider_player_key = str(api_player_id) if api_player_id is not None else compact_name(
                player_name
            )
            minutes = int_or_none(games.get("minutes")) or 0
            execute(
                conn,
                """
                INSERT INTO player_match_stats (
                    match_id, provider_player_key, source_fixture_id, local_team_id,
                    api_team_id, team_name, api_player_id, player_name, minutes,
                    position, rating, goals, assists, yellow_cards, red_cards,
                    clean_sheet, raw_json, updated_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """,
                (
                    match["id"],
                    provider_player_key,
                    api_fixture_id,
                    local_team_id,
                    api_team_id,
                    api_team.get("name"),
                    api_player_id,
                    player_name,
                    minutes,
                    games.get("position"),
                    games.get("rating"),
                    int_or_none(goals.get("total")) or 0,
                    int_or_none(goals.get("assists")) or 0,
                    int_or_none(cards.get("yellow")) or 0,
                    int_or_none(cards.get("red")) or 0,
                    bool_int(team_clean_sheet and minutes > 0),
                    json.dumps(player_block, sort_keys=True),
                ),
            )

    return {
        "match_id": match["id"],
        "fixture_id": api_fixture_id,
        "status": status_short,
        "final": final,
        "home_score": home_score,
        "away_score": away_score,
        "events": len(fixture.get("events") or []),
        "player_rows": sum(
            len(block.get("players") or []) for block in fixture.get("players") or []
        ),
    }


def run_api_football_completed_sync(
    data: dict[str, Any],
    force: bool = False,
    dry_run: bool = False,
    limit: int = API_FOOTBALL_MAX_BATCH_SIZE,
) -> dict[str, Any]:
    if not API_FOOTBALL_KEY:
        return {"ok": False, "error": "API_FOOTBALL_KEY is not configured."}

    limit = max(1, min(API_FOOTBALL_MAX_BATCH_SIZE, int(limit)))
    candidates = due_api_football_matches(data, force=force, limit=limit)
    if not candidates:
        return {"ok": True, "synced": [], "skipped": [], "linking": None, "dry_run": dry_run}

    links = api_football_fixture_links()
    missing_link_ids = [match["id"] for match in candidates if match["id"] not in links]
    linking = None
    if missing_link_ids and not dry_run:
        linking = api_football_link_fixtures(data)
        links = api_football_fixture_links()

    linked_candidates = [match for match in candidates if match["id"] in links]
    skipped = [
        {"match_id": match["id"], "reason": "missing_api_football_fixture_link"}
        for match in candidates
        if match["id"] not in links
    ]
    if dry_run:
        return {
            "ok": True,
            "dry_run": True,
            "candidates": [
                {"match_id": match["id"], "fixture_id": links.get(match["id"])}
                for match in candidates
            ],
            "skipped": skipped,
            "linking": linking,
        }
    if not linked_candidates:
        return {"ok": True, "synced": [], "skipped": skipped, "linking": linking}

    fixture_ids = [links[match["id"]] for match in linked_candidates]
    payload = api_football_get("fixtures", {"ids": "-".join(str(value) for value in fixture_ids)})
    fixture_by_id = {}
    for fixture in payload.get("response", []):
        api_fixture_id = int_or_none((fixture.get("fixture") or {}).get("id"))
        if api_fixture_id is not None:
            fixture_by_id[api_fixture_id] = fixture
    synced = []
    with get_db() as conn:
        for match in linked_candidates:
            fixture = fixture_by_id.get(links[match["id"]])
            if fixture is None:
                skipped.append({"match_id": match["id"], "reason": "fixture_not_returned"})
                continue
            synced.append(store_api_football_fixture_snapshot(conn, match, fixture, data))

    return {
        "ok": True,
        "dry_run": False,
        "synced": synced,
        "skipped": skipped,
        "linking": linking,
        "requests_today": api_football_request_count_today(),
        "daily_limit": API_FOOTBALL_DAILY_LIMIT,
    }


def api_football_team_links() -> dict[str, dict[str, Any]]:
    with get_db() as conn:
        rows = execute(
            conn,
            """
            SELECT local_team_id, api_team_id, api_team_name, confidence, linked_at
            FROM api_football_team_links
            """,
        ).fetchall()
    return {row["local_team_id"]: dict(row) for row in rows}


def seed_api_football_team_links_from_fixture_links(data: dict[str, Any]) -> int:
    matches = {match["id"]: match for match in data["matches"]}
    seeded = 0
    with get_db() as conn:
        rows = execute(
            conn,
            """
            SELECT match_id, api_home_team_id, api_away_team_id,
                   api_home_team_name, api_away_team_name, confidence
            FROM api_football_fixture_links
            """,
        ).fetchall()
        for row in rows:
            match = matches.get(row["match_id"])
            if not match:
                continue
            before = seeded
            if row["api_home_team_id"] is not None:
                upsert_api_football_team_link(
                    conn,
                    match.get("home_team_id"),
                    int(row["api_home_team_id"]),
                    row["api_home_team_name"],
                    row["confidence"],
                )
                seeded += 1
            if row["api_away_team_id"] is not None:
                upsert_api_football_team_link(
                    conn,
                    match.get("away_team_id"),
                    int(row["api_away_team_id"]),
                    row["api_away_team_name"],
                    row["confidence"],
                )
                seeded += 1
            if seeded == before:
                continue
    return seeded


def due_api_football_teams(
    data: dict[str, Any],
    force: bool = False,
    limit: int = API_FOOTBALL_SQUAD_SYNC_BATCH_SIZE,
) -> list[dict[str, Any]]:
    links = api_football_team_links()
    current = utc_now()
    due: list[dict[str, Any]] = []
    with get_db() as conn:
        snapshot_rows = execute(
            conn,
            """
            SELECT local_team_id, synced_at
            FROM api_football_team_squad_snapshots
            """,
        ).fetchall()
    synced_at_by_team = {
        row["local_team_id"]: parse_iso_datetime(row["synced_at"]) for row in snapshot_rows
    }

    for team in sorted(data["teams"], key=lambda item: item["name"]):
        link = links.get(team["id"])
        if not link:
            continue
        synced_at = synced_at_by_team.get(team["id"])
        if synced_at:
            next_refresh = synced_at + timedelta(hours=API_FOOTBALL_SQUAD_REFRESH_HOURS)
            if not force and current < next_refresh:
                continue
        due.append({"team": team, "link": link})
        if len(due) >= max(1, int(limit)):
            break
    return due


def coach_name(coach: dict[str, Any]) -> str:
    name = clean_text(coach.get("name"))
    if name:
        return name
    return clean_text(f"{coach.get('firstname', '')} {coach.get('lastname', '')}")


def store_api_football_team_profile_snapshot(
    conn: Any,
    local_team_id: str,
    api_team_id: int,
    squad_payload: dict[str, Any],
    coach_payload: dict[str, Any] | None,
) -> dict[str, Any]:
    squad_json = json.dumps(squad_payload, sort_keys=True)
    coach_json = json.dumps(coach_payload, sort_keys=True) if coach_payload else None
    execute(
        conn,
        """
        INSERT INTO api_football_team_squad_snapshots (
            local_team_id, api_team_id, squad_payload_json, coach_payload_json, synced_at
        )
        VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
        ON CONFLICT(local_team_id)
        DO UPDATE SET api_team_id = excluded.api_team_id,
                      squad_payload_json = excluded.squad_payload_json,
                      coach_payload_json = excluded.coach_payload_json,
                      synced_at = CURRENT_TIMESTAMP
        """,
        (local_team_id, api_team_id, squad_json, coach_json),
    )
    execute(
        conn,
        """
        INSERT INTO api_football_team_squad_snapshot_history (
            local_team_id, api_team_id, squad_payload_json, coach_payload_json, synced_at
        )
        VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
        """,
        (local_team_id, api_team_id, squad_json, coach_json),
    )

    execute(conn, "DELETE FROM team_squad_players WHERE local_team_id = ?", (local_team_id,))
    player_count = 0
    for squad_block in squad_payload.get("response") or []:
        team = squad_block.get("team") or {}
        source_team_id = int_or_none(team.get("id")) or api_team_id
        if source_team_id != api_team_id:
            continue
        for player in squad_block.get("players") or []:
            api_player_id = int_or_none(player.get("id"))
            player_name = clean_text(player.get("name")) or "Unknown"
            provider_player_key = str(api_player_id) if api_player_id is not None else compact_name(
                player_name
            )
            execute(
                conn,
                """
                INSERT INTO team_squad_players (
                    local_team_id, provider_player_key, source_team_id, api_player_id,
                    player_name, age, number, position, photo_url, raw_json, synced_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """,
                (
                    local_team_id,
                    provider_player_key,
                    source_team_id,
                    api_player_id,
                    player_name,
                    int_or_none(player.get("age")),
                    int_or_none(player.get("number")),
                    player.get("position"),
                    player.get("photo"),
                    json.dumps(player, sort_keys=True),
                ),
            )
            player_count += 1

    execute(conn, "DELETE FROM team_coaches WHERE local_team_id = ?", (local_team_id,))
    coach_count = 0
    if coach_payload:
        for coach in coach_payload.get("response") or []:
            api_coach_id = int_or_none(coach.get("id"))
            name = coach_name(coach) or "Unknown"
            provider_coach_key = str(api_coach_id) if api_coach_id is not None else compact_name(
                name
            )
            execute(
                conn,
                """
                INSERT INTO team_coaches (
                    local_team_id, provider_coach_key, source_team_id, api_coach_id,
                    coach_name, age, nationality, photo_url, raw_json, synced_at
                )
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """,
                (
                    local_team_id,
                    provider_coach_key,
                    api_team_id,
                    api_coach_id,
                    name,
                    int_or_none(coach.get("age")),
                    coach.get("nationality"),
                    coach.get("photo"),
                    json.dumps(coach, sort_keys=True),
                ),
            )
            coach_count += 1

    return {
        "team_id": local_team_id,
        "api_team_id": api_team_id,
        "players": player_count,
        "coaches": coach_count,
    }


def run_api_football_squad_sync(
    data: dict[str, Any],
    force: bool = False,
    dry_run: bool = False,
    limit: int = API_FOOTBALL_SQUAD_SYNC_BATCH_SIZE,
) -> dict[str, Any]:
    if not API_FOOTBALL_KEY:
        return {"ok": False, "error": "API_FOOTBALL_KEY is not configured."}

    limit = max(1, min(48, int(limit)))
    links = api_football_team_links()
    linking = None
    if len(links) < len(data.get("teams", [])):
        seeded = seed_api_football_team_links_from_fixture_links(data)
        links = api_football_team_links()
        linking = {"seeded_from_fixture_links": seeded}
    if len(links) < len(data.get("teams", [])) and not dry_run:
        next_linking: dict[str, Any] = dict(linking or {})
        next_linking["fixture_linking"] = api_football_link_fixtures(data)
        linking = next_linking
        links = api_football_team_links()

    candidates = due_api_football_teams(data, force=force, limit=limit)
    skipped = [
        {"team_id": team["id"], "reason": "missing_api_football_team_link"}
        for team in data.get("teams", [])
        if team["id"] not in links
    ]
    if dry_run:
        return {
            "ok": True,
            "dry_run": True,
            "candidates": [
                {
                    "team_id": item["team"]["id"],
                    "team_name": item["team"]["name"],
                    "api_team_id": item["link"]["api_team_id"],
                }
                for item in candidates
            ],
            "skipped": skipped,
            "linking": linking,
        }

    synced = []
    with get_db() as conn:
        for item in candidates:
            local_team_id = item["team"]["id"]
            api_team_id = int(item["link"]["api_team_id"])
            squad_payload = api_football_get("players/squads", {"team": api_team_id})
            try:
                coach_payload = api_football_get("coachs", {"team": api_team_id})
            except Exception as error:
                logger.warning("Could not sync coach for %s: %s", local_team_id, error)
                coach_payload = None
            synced.append(
                store_api_football_team_profile_snapshot(
                    conn, local_team_id, api_team_id, squad_payload, coach_payload
                )
            )

    return {
        "ok": True,
        "dry_run": False,
        "synced": synced,
        "skipped": skipped,
        "linking": linking,
        "requests_today": api_football_request_count_today(),
        "daily_limit": API_FOOTBALL_DAILY_LIMIT,
    }


def local_match_date(match: dict[str, Any]) -> Any:
    return match_kickoff(match).astimezone(AMSTERDAM_TZ).date()


def score_rule_for_match(match: dict[str, Any]) -> dict[str, int]:
    return MATCH_SCORE_RULES.get(match["round"], MATCH_SCORE_RULES["Group Stage"])


def match_prediction_points(prediction: Any, match: dict[str, Any]) -> tuple[int, str | None]:
    result = match_result(match)
    if result is None:
        return 0, None
    rule = score_rule_for_match(match)
    exact_score = prediction["home_score"] == match.get("home_score") and prediction[
        "away_score"
    ] == match.get("away_score")
    if exact_score:
        return rule["exact"], "exact"
    if prediction_result(prediction) == result:
        return rule["outcome"], "outcome"
    return 0, None


def quiz_complete(quiz: dict[str, Any] | None, prediction: Any | None) -> bool:
    if not quiz:
        return True
    answer = clean_text(prediction["answer"] if prediction else "")
    if not answer:
        return False
    if quiz.get("viewership") and prediction:
        return prediction["viewership_prediction"] is not None
    return True


def quiz_answer_points(quiz: dict[str, Any], prediction: Any | None) -> int:
    if not prediction:
        return 0
    correct_answers = quiz.get("correct_answers")
    if correct_answers is None and quiz.get("correct_answer") is not None:
        correct_answers = [quiz.get("correct_answer")]
    if not correct_answers:
        return 0
    user_answer = normalize_answer(prediction["answer"])
    normalized_correct = {normalize_answer(answer) for answer in correct_answers}
    if user_answer not in normalized_correct:
        return 0
    choice_points = quiz.get("choice_points") or {}
    for choice, points in choice_points.items():
        if normalize_answer(choice) == user_answer:
            return int(points)
    dynamic_choice_points = quiz.get("dynamic_choice_points")
    if dynamic_choice_points is not None:
        return int(dynamic_choice_points)
    return QUIZ_YES_NO_POINTS if quiz.get("type") == "yes_no" else QUIZ_OPEN_POINTS


def quiz_viewership_winners(
    data: dict[str, Any], quiz_predictions: list[Any]
) -> set[tuple[int, str]]:
    predictions_by_match: dict[str, list[Any]] = {}
    for prediction in quiz_predictions:
        if prediction["viewership_prediction"] is not None:
            predictions_by_match.setdefault(prediction["match_id"], []).append(prediction)

    winners = set()
    for match in data["matches"]:
        quiz = match.get("quiz")
        if not quiz or quiz.get("viewership_answer") is None:
            continue
        try:
            correct_value = int(quiz["viewership_answer"])
        except (TypeError, ValueError):
            continue
        match_predictions = predictions_by_match.get(match["id"], [])
        if not match_predictions:
            continue
        deltas = [
            (abs(int(row["viewership_prediction"]) - correct_value), row)
            for row in match_predictions
        ]
        closest_delta = min(delta for delta, _ in deltas)
        for delta, row in deltas:
            if delta == closest_delta:
                winners.add((row["user_id"], row["match_id"]))
    return winners


def quiz_points_for_prediction(
    match: dict[str, Any], prediction: Any | None, viewership_winners: set[tuple[int, str]]
) -> int:
    quiz = match.get("quiz")
    if not quiz:
        return 0
    points = quiz_answer_points(quiz, prediction)
    if prediction and (prediction["user_id"], prediction["match_id"]) in viewership_winners:
        points += QUIZ_VIEWERSHIP_POINTS
    return points


def standings_from_scores(
    group: dict[str, Any],
    matches: list[dict[str, Any]],
    scores_by_match: dict[str, tuple[int, int]],
) -> list[str]:
    rows = {
        team_id: {
            "team_id": team_id,
            "played": 0,
            "points": 0,
            "goals_for": 0,
            "goals_against": 0,
        }
        for team_id in group["teams"]
    }
    for match in matches:
        scores = scores_by_match.get(match["id"])
        if scores is None:
            continue
        home_score, away_score = scores
        home = rows.get(match["home_team_id"])
        away = rows.get(match["away_team_id"])
        if home is None or away is None:
            continue
        home["played"] += 1
        away["played"] += 1
        home["goals_for"] += home_score
        home["goals_against"] += away_score
        away["goals_for"] += away_score
        away["goals_against"] += home_score
        if home_score > away_score:
            home["points"] += 3
        elif home_score < away_score:
            away["points"] += 3
        else:
            home["points"] += 1
            away["points"] += 1

    ordered = sorted(
        rows.values(),
        key=lambda row: (
            -row["points"],
            -(row["goals_for"] - row["goals_against"]),
            -row["goals_for"],
            row["team_id"],
        ),
    )
    return [row["team_id"] for row in ordered]


def group_position_score(
    user_predictions: dict[str, Any], data: dict[str, Any]
) -> tuple[int, int]:
    points = 0
    correct_positions = 0
    group_matches_by_id = {
        match["id"]: match for match in data["matches"] if match["round"] == "Group Stage"
    }
    for group in data["groups"]:
        matches = [
            match
            for match in group_matches_by_id.values()
            if match.get("group") == group["id"]
        ]
        if not matches:
            continue
        if any(match_result(match) is None for match in matches):
            continue
        if any(match["id"] not in user_predictions for match in matches):
            continue
        actual_scores = {
            match["id"]: (match["home_score"], match["away_score"]) for match in matches
        }
        predicted_scores = {
            match["id"]: (
                user_predictions[match["id"]]["home_score"],
                user_predictions[match["id"]]["away_score"],
            )
            for match in matches
        }
        actual_order = standings_from_scores(group, matches, actual_scores)
        predicted_order = standings_from_scores(group, matches, predicted_scores)
        for actual_team, predicted_team in zip(actual_order, predicted_order, strict=False):
            if actual_team == predicted_team:
                correct_positions += 1
                points += GROUP_POSITION_POINTS
    return points, correct_positions


BADGE_DEFINITIONS = {
    "perfect_score": {
        "label": "Perfect Score",
        "detail": "Exacte uitslag goed voorspeld.",
        "family": "zayu",
        "mascot": "Zayu Jaguar",
        "mark": "Z",
    },
    "hattrick_hero": {
        "label": "Hattrick Hero",
        "detail": "Drie exacte uitslagen op rij.",
        "family": "zayu",
        "mascot": "Zayu Jaguar",
        "mark": "Z",
    },
    "on_fire": {
        "label": "On Fire",
        "detail": "Drie toto's op rij goed.",
        "family": "zayu",
        "mascot": "Zayu Jaguar",
        "mark": "Z",
    },
    "oranje_treffer": {
        "label": "Oranje Treffer",
        "detail": "Juiste toto bij een wedstrijd van Nederland.",
        "family": "oranje",
        "mascot": "Oranje Leeuw",
        "mark": "NL",
    },
    "oranje_expert": {
        "label": "Oranje Expert",
        "detail": "Exacte uitslag bij een wedstrijd van Nederland.",
        "family": "oranje",
        "mascot": "Oranje Leeuw",
        "mark": "NL",
    },
    "better_next_time": {
        "label": "Better Next Time",
        "detail": "Drie toto's op rij mis.",
        "family": "maple",
        "mascot": "Maple Moose",
        "mark": "M",
    },
    "keep_your_head_up": {
        "label": "Keep your head up",
        "detail": "Vijf keer op rij geen exacte uitslag.",
        "family": "maple",
        "mascot": "Maple Moose",
        "mark": "M",
    },
    "so_close": {
        "label": "So close",
        "detail": "Drie keer op rij maar een doelpunt naast exact.",
        "family": "maple",
        "mascot": "Maple Moose",
        "mark": "M",
    },
    "great_ranker": {
        "label": "Great Ranker",
        "detail": "Een land op de juiste positie in de poule voorspeld.",
        "family": "clutch",
        "mascot": "Clutch Eagle",
        "mark": "C",
    },
    "champ_of_the_day": {
        "label": "Champ of the day",
        "detail": "Bovenaan de league na een speeldag.",
        "family": "trophy",
        "mascot": "WK bokaal",
        "mark": "WC",
    },
}


def add_badge(counter: Counter[str], key: str, amount: int = 1) -> None:
    if amount > 0:
        counter[key] += amount


def close_score_miss(prediction: Any, match: dict[str, Any]) -> bool:
    if match_result(match) is None:
        return False
    goal_delta = abs(prediction["home_score"] - match["home_score"]) + abs(
        prediction["away_score"] - match["away_score"]
    )
    return goal_delta == 1


def materialize_badges(counter: Counter[str]) -> list[dict[str, Any]]:
    badges = []
    for key, definition in BADGE_DEFINITIONS.items():
        count = counter[key]
        if count <= 0:
            continue
        badges.append({"key": key, "count": count, **definition})
    return badges


def badge_catalog() -> list[dict[str, Any]]:
    return [{"key": key, **definition} for key, definition in BADGE_DEFINITIONS.items()]


def badge_counters_and_metrics(
    data: dict[str, Any],
    user_predictions: list[Any],
    correct_group_positions: int,
    champ_days: int,
) -> tuple[Counter[str], dict[str, dict[str, Any]]]:
    matches = {match["id"]: match for match in data["matches"]}
    completed_predictions = sorted(
        [
            prediction
            for prediction in user_predictions
            if match_result(matches.get(prediction["match_id"], {})) is not None
        ],
        key=lambda prediction: match_kickoff(matches[prediction["match_id"]]),
    )
    counter: Counter[str] = Counter()
    exact_streak = 0
    outcome_streak = 0
    wrong_outcome_streak = 0
    wrong_exact_streak = 0
    close_miss_streak = 0
    max_exact_streak = 0
    max_outcome_streak = 0
    max_wrong_outcome_streak = 0
    max_wrong_exact_streak = 0
    max_close_miss_streak = 0
    exact_count = 0
    netherlands_outcomes = 0
    netherlands_exacts = 0

    for prediction in completed_predictions:
        match = matches[prediction["match_id"]]
        points, score_kind = match_prediction_points(prediction, match)
        exact = score_kind == "exact"
        outcome = points > 0 and prediction_result(prediction) == match_result(match)
        netherlands_match = (
            match.get("home_team_id") == NETHERLANDS_TEAM_ID
            or match.get("away_team_id") == NETHERLANDS_TEAM_ID
        )

        if exact:
            exact_count += 1
            add_badge(counter, "perfect_score")
            exact_streak += 1
            wrong_exact_streak = 0
            close_miss_streak = 0
            if exact_streak >= 3:
                add_badge(counter, "hattrick_hero")
        else:
            exact_streak = 0
            wrong_exact_streak += 1
            if wrong_exact_streak >= 5:
                add_badge(counter, "keep_your_head_up")
            if close_score_miss(prediction, match):
                close_miss_streak += 1
                if close_miss_streak >= 3:
                    add_badge(counter, "so_close")
            else:
                close_miss_streak = 0

        if outcome:
            outcome_streak += 1
            wrong_outcome_streak = 0
            if outcome_streak >= 3:
                add_badge(counter, "on_fire")
            if netherlands_match:
                netherlands_outcomes += 1
                add_badge(counter, "oranje_treffer")
        else:
            outcome_streak = 0
            wrong_outcome_streak += 1
            if wrong_outcome_streak >= 3:
                add_badge(counter, "better_next_time")

        if exact and netherlands_match:
            netherlands_exacts += 1
            add_badge(counter, "oranje_expert")

        max_exact_streak = max(max_exact_streak, exact_streak)
        max_outcome_streak = max(max_outcome_streak, outcome_streak)
        max_wrong_outcome_streak = max(max_wrong_outcome_streak, wrong_outcome_streak)
        max_wrong_exact_streak = max(max_wrong_exact_streak, wrong_exact_streak)
        max_close_miss_streak = max(max_close_miss_streak, close_miss_streak)

    add_badge(counter, "great_ranker", correct_group_positions)
    add_badge(counter, "champ_of_the_day", champ_days)

    metrics = {
        "perfect_score": {"current": exact_count, "target": 1, "unit": "exact score"},
        "hattrick_hero": {
            "current": max_exact_streak,
            "target": 3,
            "unit": "exact scores in a row",
        },
        "on_fire": {
            "current": max_outcome_streak,
            "target": 3,
            "unit": "correct outcomes in a row",
        },
        "oranje_treffer": {
            "current": netherlands_outcomes,
            "target": 1,
            "unit": "Netherlands outcome",
        },
        "oranje_expert": {
            "current": netherlands_exacts,
            "target": 1,
            "unit": "Netherlands exact score",
        },
        "better_next_time": {
            "current": max_wrong_outcome_streak,
            "target": 3,
            "unit": "wrong outcomes in a row",
        },
        "keep_your_head_up": {
            "current": max_wrong_exact_streak,
            "target": 5,
            "unit": "non-exact scores in a row",
        },
        "so_close": {
            "current": max_close_miss_streak,
            "target": 3,
            "unit": "one-goal misses in a row",
        },
        "great_ranker": {
            "current": correct_group_positions,
            "target": 1,
            "unit": "correct group position",
        },
        "champ_of_the_day": {
            "current": champ_days,
            "target": 1,
            "unit": "day won",
        },
    }
    return counter, metrics


def badge_progress_list(
    data: dict[str, Any],
    user_predictions: list[Any],
    correct_group_positions: int,
    champ_days: int,
) -> list[dict[str, Any]]:
    counter, metrics = badge_counters_and_metrics(
        data,
        user_predictions,
        correct_group_positions,
        champ_days,
    )
    progress = []
    for key, definition in BADGE_DEFINITIONS.items():
        metric = metrics[key]
        current = int(metric["current"])
        target = max(1, int(metric["target"]))
        progress.append(
            {
                "key": key,
                "count": counter[key],
                "unlocked": counter[key] > 0,
                "current": current,
                "target": target,
                "unit": metric["unit"],
                "progress": min(100, round((current / target) * 100)),
                **definition,
            }
        )
    return progress


def score_through_date(
    data: dict[str, Any],
    user_predictions: list[Any],
    user_quiz_predictions: dict[str, Any],
    user_leeuwtjes: set[str],
    viewership_winners: set[tuple[int, str]],
    target_date: Any,
) -> int:
    matches = {match["id"]: match for match in data["matches"]}
    points = 0
    for prediction in user_predictions:
        match = matches.get(prediction["match_id"])
        if not match or match_result(match) is None or local_match_date(match) > target_date:
            continue
        base_points, _ = match_prediction_points(prediction, match)
        points += base_points * (2 if prediction["match_id"] in user_leeuwtjes else 1)

    for match in data["matches"]:
        if match_result(match) is None or local_match_date(match) > target_date:
            continue
        points += quiz_points_for_prediction(
            match, user_quiz_predictions.get(match["id"]), viewership_winners
        )
    return points


def champion_day_counts(
    data: dict[str, Any],
    users: list[Any],
    by_user: dict[int, list[Any]],
    quiz_by_user: dict[int, dict[str, Any]],
    leeuwtjes_by_user: dict[int, set[str]],
    viewership_winners: set[tuple[int, str]],
) -> Counter[int]:
    completed_dates = sorted(
        {
            local_match_date(match)
            for match in data["matches"]
            if match_result(match) is not None
        }
    )
    counts: Counter[int] = Counter()
    for completed_date in completed_dates:
        daily_scores = {
            user["id"]: score_through_date(
                data,
                by_user.get(user["id"], []),
                quiz_by_user.get(user["id"], {}),
                leeuwtjes_by_user.get(user["id"], set()),
                viewership_winners,
                completed_date,
            )
            for user in users
        }
        top_score = max(daily_scores.values(), default=0)
        if top_score <= 0:
            continue
        for user_id, score in daily_scores.items():
            if score == top_score:
                counts[user_id] += 1
    return counts


def badge_list(
    data: dict[str, Any],
    user_predictions: list[Any],
    correct_group_positions: int,
    champ_days: int,
) -> list[dict[str, Any]]:
    counter, _ = badge_counters_and_metrics(
        data,
        user_predictions,
        correct_group_positions,
        champ_days,
    )
    return materialize_badges(counter)


def initials(name: str) -> str:
    parts = [part for part in name.replace("-", " ").split() if part]
    if not parts:
        return "?"
    return "".join(part[0] for part in parts[:2]).upper()


def avatar_hue(name: str) -> int:
    return sum(ord(char) for char in name) % 360


def require_current_user(
    error_message: str = "Log in before using this feature.",
) -> tuple[dict[str, Any] | None, Any | None]:
    user = current_user()
    if not user:
        return None, (jsonify({"error": error_message}), 401)
    return user, None


def sync_token_from_request() -> str:
    auth_header = request.headers.get("Authorization", "")
    if auth_header.casefold().startswith("bearer "):
        return auth_header.split(" ", 1)[1].strip()
    return request.headers.get("X-WK-HUB-SYNC-TOKEN", "") or request.args.get("token", "")


def require_sync_token() -> Any | None:
    if not API_FOOTBALL_SYNC_TOKEN:
        return jsonify({"error": "WK_HUB_SYNC_TOKEN or CRON_SECRET is not configured."}), 503
    if sync_token_from_request() != API_FOOTBALL_SYNC_TOKEN:
        return jsonify({"error": "Invalid sync token."}), 403
    return None


def social_state(user: dict[str, Any]) -> dict[str, Any]:
    with get_db() as conn:
        users = execute(
            conn,
            "SELECT id, name, email, profile_image_url FROM users WHERE id != ? ORDER BY name",
            (user["id"],),
        ).fetchall()
        follows = execute(conn, "SELECT follower_id, followed_id FROM user_follows").fetchall()

    following = {row["followed_id"] for row in follows if row["follower_id"] == user["id"]}
    followers = {row["follower_id"] for row in follows if row["followed_id"] == user["id"]}
    friends = following & followers

    people = []
    for row in users:
        is_following = row["id"] in following
        follows_me = row["id"] in followers
        is_friend = row["id"] in friends
        relationship = "none"
        if is_friend:
            relationship = "friend"
        elif is_following:
            relationship = "following"
        elif follows_me:
            relationship = "follows_you"

        people.append(
            {
                "user_id": row["id"],
                "name": row["name"],
                "profile_picture": user_profile_picture(row),
                "is_following": is_following,
                "follows_me": follows_me,
                "is_friend": is_friend,
                "relationship": relationship,
            }
        )

    return {
        "people": people,
        "counts": {
            "following": len(following),
            "followers": len(followers),
            "friends": len(friends),
        },
    }


def users_are_friends(user_id: int, other_user_id: int) -> bool:
    if user_id == other_user_id:
        return True
    with get_db() as conn:
        row = execute(
            conn,
            """
            SELECT 1
            FROM user_follows outbound
            JOIN user_follows inbound
              ON inbound.follower_id = outbound.followed_id
             AND inbound.followed_id = outbound.follower_id
            WHERE outbound.follower_id = ?
              AND outbound.followed_id = ?
            """,
            (user_id, other_user_id),
        ).fetchone()
    return row is not None


def user_prediction_groups(
    profile_user_id: int,
    data: dict[str, Any],
    include_unplayed: bool = False,
) -> list[dict[str, Any]]:
    teams = {team["id"]: team for team in data["teams"]}

    with get_db() as conn:
        rows = execute(
            conn,
            """
            SELECT match_id, home_score, away_score
            FROM match_predictions
            WHERE user_id = ?
            """,
            (profile_user_id,),
        ).fetchall()
        quiz_rows = execute(
            conn,
            """
            SELECT match_id, answer, viewership_prediction
            FROM quiz_predictions
            WHERE user_id = ?
            """,
            (profile_user_id,),
        ).fetchall()
        leeuwtje_rows = execute(
            conn,
            "SELECT match_id FROM leeuwtje_predictions WHERE user_id = ?",
            (profile_user_id,),
        ).fetchall()

    by_match = {row["match_id"]: row for row in rows}
    quiz_by_match = {row["match_id"]: row for row in quiz_rows}
    leeuwtjes = {row["match_id"] for row in leeuwtje_rows}
    groups = []
    for group in data["groups"]:
        group_predictions = []
        group_matches = sorted(
            [
                match
                for match in data["matches"]
                if match["round"] == "Group Stage" and match.get("group") == group["id"]
            ],
            key=match_kickoff,
        )
        for match in group_matches:
            if not include_unplayed and match_result(match) is None:
                continue
            prediction = by_match.get(match["id"])
            if prediction is None:
                continue
            quiz_prediction = quiz_by_match.get(match["id"])
            group_predictions.append(
                {
                    "match_id": match["id"],
                    "date": match["date"],
                    "time_utc": match["time_utc"],
                    "home_team_id": match["home_team_id"],
                    "away_team_id": match["away_team_id"],
                    "home_team_name": teams.get(match["home_team_id"], {}).get(
                        "name", match["home_team_id"]
                    ),
                    "away_team_name": teams.get(match["away_team_id"], {}).get(
                        "name", match["away_team_id"]
                    ),
                    "home_score": prediction["home_score"],
                    "away_score": prediction["away_score"],
                    "quiz_question": match.get("quiz", {}).get("question"),
                    "quiz_answer": quiz_prediction["answer"] if quiz_prediction else None,
                    "viewership_prediction": (
                        quiz_prediction["viewership_prediction"] if quiz_prediction else None
                    ),
                    "leeuwtje": match["id"] in leeuwtjes,
                }
            )
        if group_predictions:
            groups.append({"group": group["id"], "predictions": group_predictions})
    return groups


def build_leaderboard(data: dict[str, Any]) -> list[dict[str, Any]]:
    matches = {match["id"]: match for match in data["matches"]}
    teams = {team["id"]: team for team in data["teams"]}
    champion_id = data.get("meta", {}).get("world_cup_winner_id")
    top_scorer_result = top_scorer_result_name(data)
    eliminated_teams = eliminated_team_ids(data)
    group_stage_ids = {match["id"] for match in data["matches"] if match["round"] == "Group Stage"}
    required_group_id = next(
        (group["id"] for group in data["groups"] if NETHERLANDS_TEAM_ID in group["teams"]),
        None,
    )
    required_group_ids = {
        match["id"]
        for match in data["matches"]
        if match["round"] == "Group Stage" and match.get("group") == required_group_id
    }

    with get_db() as conn:
        users = execute(
            conn, "SELECT id, name, email, profile_image_url FROM users ORDER BY name"
        ).fetchall()
        predictions = execute(conn, "SELECT * FROM match_predictions").fetchall()
        quiz_predictions = execute(conn, "SELECT * FROM quiz_predictions").fetchall()
        leeuwtjes = execute(conn, "SELECT user_id, match_id FROM leeuwtje_predictions").fetchall()
        winners = {
            row["user_id"]: row["team_id"]
            for row in execute(conn, "SELECT user_id, team_id FROM winner_predictions").fetchall()
        }
        top_scorers = {
            row["user_id"]: row
            for row in execute(
                conn,
                """
                SELECT user_id, player_name, player_name_2, player_name_3,
                       striker_name_1, striker_name_2, striker_name_3,
                       striker_name_4, striker_name_5
                FROM top_scorer_predictions
                """,
            ).fetchall()
        }

    by_user: dict[int, list[Any]] = {}
    for prediction in predictions:
        by_user.setdefault(prediction["user_id"], []).append(prediction)
    quiz_by_user: dict[int, dict[str, Any]] = {}
    for prediction in quiz_predictions:
        quiz_by_user.setdefault(prediction["user_id"], {})[prediction["match_id"]] = prediction
    leeuwtjes_by_user: dict[int, set[str]] = {}
    for row in leeuwtjes:
        leeuwtjes_by_user.setdefault(row["user_id"], set()).add(row["match_id"])
    viewership_winners = quiz_viewership_winners(data, list(quiz_predictions))
    champ_days_by_user = champion_day_counts(
        data,
        list(users),
        by_user,
        quiz_by_user,
        leeuwtjes_by_user,
        viewership_winners,
    )

    goal_counts = goal_counts_by_player()
    leaderboard = []
    for user in users:
        points = 0
        exact_scores = 0
        outcomes = 0
        shooting = 0
        defence = 0
        scoring_games = 0
        user_predictions = by_user.get(user["id"], [])
        user_predictions_by_match = {
            prediction["match_id"]: prediction for prediction in user_predictions
        }
        user_quiz_predictions = quiz_by_user.get(user["id"], {})
        user_leeuwtjes = leeuwtjes_by_user.get(user["id"], set())
        user_prediction_ids = {prediction["match_id"] for prediction in user_predictions}
        group_stage_predictions = sum(
            1 for match_id in user_prediction_ids if match_id in group_stage_ids
        )
        required_group_predictions = sum(
            1 for match_id in user_prediction_ids if match_id in required_group_ids
        )
        required_group_complete = bool(required_group_ids) and required_group_predictions >= len(
            required_group_ids
        )
        if not required_group_complete:
            continue

        for prediction in user_predictions:
            match = matches.get(prediction["match_id"])
            if match is None:
                continue
            result = match_result(match)
            if result is None:
                continue
            base_points, score_kind = match_prediction_points(prediction, match)
            if prediction["match_id"] in user_leeuwtjes:
                points += base_points * 2
            else:
                points += base_points
            if score_kind == "exact":
                exact_scores += 1
                scoring_games += 1
            elif score_kind == "outcome":
                outcomes += 1
                scoring_games += 1

            if result > 0:
                if prediction["home_score"] == match.get("home_score"):
                    shooting += 1
                if prediction["away_score"] == match.get("away_score"):
                    defence += 1
            elif result < 0:
                if prediction["away_score"] == match.get("away_score"):
                    shooting += 1
                if prediction["home_score"] == match.get("home_score"):
                    defence += 1

        group_position_points, correct_group_positions = group_position_score(
            user_predictions_by_match, data
        )
        points += group_position_points

        quiz_points = 0
        quiz_answer_count = 0
        for match in data["matches"]:
            quiz = match.get("quiz")
            if not quiz:
                continue
            quiz_prediction = user_quiz_predictions.get(match["id"])
            if quiz_complete(quiz, quiz_prediction):
                quiz_answer_count += 1
            quiz_points += quiz_points_for_prediction(match, quiz_prediction, viewership_winners)
        points += quiz_points

        winner_pick = winners.get(user["id"])
        winner_points = WINNER_POINTS if champion_id and winner_pick == champion_id else 0
        points += winner_points
        winner_impossible = bool(
            winner_pick
            and (
                (champion_id and winner_pick != champion_id)
                or winner_pick in eliminated_teams
            )
        )
        top_scorer_pick_row = top_scorers.get(user["id"])
        top_scorer_pick = top_scorer_pick_name(top_scorer_pick_row)
        striker_picks = striker_pick_score_rows(top_scorer_pick_row, goal_counts)
        top_scorer_points = top_scorer_prediction_points(data, top_scorer_pick)
        top_scorer_impossible = bool(
            top_scorer_pick
            and top_scorer_result
            and normalize_answer(top_scorer_pick) != normalize_answer(top_scorer_result)
        )
        striker_points = sum(pick["points"] for pick in striker_picks)
        scorer_points = top_scorer_points + striker_points
        points += scorer_points
        all_group_predictions_complete = group_stage_predictions >= len(group_stage_ids)
        leeuwtje_points = 0
        for prediction in user_predictions:
            if prediction["match_id"] not in user_leeuwtjes:
                continue
            match = matches.get(prediction["match_id"])
            if match is None:
                continue
            base_points, _ = match_prediction_points(prediction, match)
            leeuwtje_points += base_points
        champ_days = champ_days_by_user[user["id"]]
        badges = badge_list(
            data,
            user_predictions,
            correct_group_positions,
            champ_days,
        )

        leaderboard.append(
            {
                "user_id": user["id"],
                "name": user["name"],
                "profile_picture": user_profile_picture(user),
                "points": points,
                "exact_scores": exact_scores,
                "precision": exact_scores,
                "shooting": shooting,
                "defence": defence,
                "scoring_games": scoring_games,
                "outcomes": outcomes,
                "quiz_points": quiz_points,
                "quiz_answers": quiz_answer_count,
                "group_position_points": group_position_points,
                "group_positions_correct": correct_group_positions,
                "leeuwtjes_used": len(user_leeuwtjes),
                "leeuwtje_points": leeuwtje_points,
                "predictions_count": len(user_predictions),
                "group_stage_predictions": group_stage_predictions,
                "group_stage_total": len(group_stage_ids),
                "required_group_predictions": required_group_predictions,
                "required_group_total": len(required_group_ids),
                "all_predictions_complete": all_group_predictions_complete,
                "entry_complete": (
                    all_group_predictions_complete
                    and winner_pick is not None
                    and bool(top_scorer_pick)
                    and len(striker_picks) >= STRIKER_PICK_COUNT
                ),
                "missing_group_stage_predictions": max(
                    0, len(group_stage_ids) - group_stage_predictions
                ),
                "winner_pick": winner_pick,
                "winner_pick_name": teams.get(winner_pick, {}).get("name") if winner_pick else None,
                "winner_points": winner_points,
                "winner_impossible": winner_impossible,
                "top_scorer_pick": top_scorer_pick or None,
                "top_scorer_points": top_scorer_points,
                "top_scorer_impossible": top_scorer_impossible,
                "striker_picks": striker_picks,
                "striker_points": striker_points,
                "scorer_points": scorer_points,
                "top_scorer_picks": striker_picks,
                "badges": badges,
                "badge_count": len(badges),
                "badge_progress": badge_progress_list(
                    data,
                    user_predictions,
                    correct_group_positions,
                    champ_days,
                ),
            }
        )

    ranked = sorted(leaderboard, key=lambda row: (-row["points"], row["name"].lower()))
    completed_dates = sorted(
        {
            local_match_date(match)
            for match in data["matches"]
            if match_result(match) is not None
        }
    )
    previous_rank_by_user: dict[int, int] = {}
    if len(completed_dates) >= 2:
        previous_date = completed_dates[-2]
        eligible_user_ids = {row["user_id"] for row in ranked}
        previous_scores = {
            user["id"]: score_through_date(
                data,
                by_user.get(user["id"], []),
                quiz_by_user.get(user["id"], {}),
                leeuwtjes_by_user.get(user["id"], set()),
                viewership_winners,
                previous_date,
            )
            for user in users
            if user["id"] in eligible_user_ids
        }
        previous_order = sorted(
            ranked,
            key=lambda row: (-previous_scores.get(row["user_id"], 0), row["name"].lower()),
        )
        previous_rank_by_user = {
            row["user_id"]: index + 1 for index, row in enumerate(previous_order)
        }

    for index, row in enumerate(ranked, start=1):
        previous_rank = previous_rank_by_user.get(row["user_id"], index)
        row["rank"] = index
        row["rank_previous"] = previous_rank
        row["rank_movement"] = previous_rank - index

    return ranked


def build_notifications(
    data: dict[str, Any],
    predictions: dict[str, dict[str, Any]],
    quiz_predictions: dict[str, Any],
    now: datetime | None = None,
) -> list[dict[str, Any]]:
    current = now or utc_now()
    today = current.astimezone(AMSTERDAM_TZ).date()
    visible_dates = {today, today + timedelta(days=1)}
    relevant_matches = [
        match
        for match in data["matches"]
        if local_match_date(match) in visible_dates
        and match.get("home_team_id")
        and match.get("away_team_id")
        and not is_prediction_locked(match, current)
    ]
    missing_predictions = [match for match in relevant_matches if match["id"] not in predictions]
    missing_quizzes = [
        match
        for match in relevant_matches
        if match.get("quiz") and not quiz_complete(match["quiz"], quiz_predictions.get(match["id"]))
    ]

    notifications = []
    if missing_predictions:
        notifications.append(
            {
                "type": "predictions",
                "count": len(missing_predictions),
                "match_ids": [match["id"] for match in missing_predictions],
                "title": "Wedstrijdvoorspellingen open",
                "body": (
                    f"{len(missing_predictions)} wedstrijd"
                    f"{'' if len(missing_predictions) == 1 else 'en'} "
                    f"{'moet' if len(missing_predictions) == 1 else 'moeten'} "
                    "nog ingevuld worden."
                ),
            }
        )
    if missing_quizzes:
        notifications.append(
            {
                "type": "quiz",
                "count": len(missing_quizzes),
                "match_ids": [match["id"] for match in missing_quizzes],
                "title": "Quizvragen open",
                "body": (
                    f"{len(missing_quizzes)} quizvraag"
                    f"{'' if len(missing_quizzes) == 1 else 'en'} "
                    f"{'moet' if len(missing_quizzes) == 1 else 'moeten'} "
                    "nog ingevuld worden."
                ),
            }
        )
    return notifications[:2]


def outcome_bucket(prediction: Any) -> str:
    result = prediction_result(prediction)
    if result > 0:
        return "home"
    if result < 0:
        return "away"
    return "draw"


def build_matchday_summary(
    data: dict[str, Any],
    user_id: int | None = None,
    now: datetime | None = None,
) -> dict[str, Any]:
    current = now or utc_now()
    today = current.astimezone(AMSTERDAM_TZ).date()
    matches_with_dates = [(local_match_date(match), match) for match in data["matches"]]
    match_dates = sorted({match_date for match_date, _ in matches_with_dates})
    target_date = today if today in match_dates else None
    if target_date is None:
        target_date = next((match_date for match_date in match_dates if match_date > today), None)
    if target_date is None and match_dates:
        target_date = match_dates[-1]

    if target_date is None:
        return {"available": False, "matches": []}

    # Build the matchday as a "playing session": start from the target date's
    # matches, then keep absorbing later matches while the gap to the previous
    # kickoff stays under MATCHDAY_SESSION_GAP. This rolls overnight matches that
    # fall on the next calendar day (Dutch time) into the same matchday, while the
    # large daytime gap stops the session before the next evening's matches.
    ordered = sorted(matches_with_dates, key=lambda item: match_kickoff(item[1]))
    target_matches = []
    previous_kickoff: datetime | None = None
    for match_date, match in ordered:
        if match_date < target_date:
            continue
        kickoff = match_kickoff(match)
        if match_date > target_date:
            if previous_kickoff is None or kickoff - previous_kickoff >= MATCHDAY_SESSION_GAP:
                break
        previous_kickoff = kickoff
        if match.get("home_team_id") and match.get("away_team_id"):
            target_matches.append(match)
    target_ids = {match["id"] for match in target_matches}

    with get_db() as conn:
        predictions = execute(
            conn,
            "SELECT user_id, match_id, home_score, away_score FROM match_predictions",
        ).fetchall()
        quiz_predictions = execute(
            conn,
            "SELECT user_id, match_id FROM quiz_predictions WHERE COALESCE(answer, '') != ''",
        ).fetchall()
        leeuwtjes = execute(conn, "SELECT user_id, match_id FROM leeuwtje_predictions").fetchall()
        my_predictions = (
            execute(
                conn,
                "SELECT match_id FROM match_predictions WHERE user_id = ?",
                (user_id,),
            ).fetchall()
            if user_id is not None
            else []
        )

    predictions_by_match: dict[str, list[Any]] = {}
    for prediction in predictions:
        if prediction["match_id"] in target_ids:
            predictions_by_match.setdefault(prediction["match_id"], []).append(prediction)
    quiz_counts = Counter(
        row["match_id"] for row in quiz_predictions if row["match_id"] in target_ids
    )
    leeuwtje_counts = Counter(row["match_id"] for row in leeuwtjes if row["match_id"] in target_ids)
    my_prediction_ids = {row["match_id"] for row in my_predictions if row["match_id"] in target_ids}

    matches = []
    for match in sorted(target_matches, key=match_kickoff):
        match_predictions = predictions_by_match.get(match["id"], [])
        outcomes = Counter(outcome_bucket(prediction) for prediction in match_predictions)
        matches.append(
            {
                "match_id": match["id"],
                "id": match["id"],
                "date": match["date"],
                "time_utc": match["time_utc"],
                "home_team_id": match["home_team_id"],
                "away_team_id": match["away_team_id"],
                "round": match["round"],
                "group": match.get("group"),
                "venue_id": match.get("venue_id"),
                "quiz": match.get("quiz"),
                "locked": is_prediction_locked(match, current),
                "has_my_prediction": match["id"] in my_prediction_ids,
                "prediction_count": len(match_predictions),
                "home_win_count": outcomes["home"],
                "draw_count": outcomes["draw"],
                "away_win_count": outcomes["away"],
                "quiz_answer_count": quiz_counts[match["id"]],
                "leeuwtjes_count": leeuwtje_counts[match["id"]],
            }
        )

    return {
        "available": True,
        "date": target_date.isoformat(),
        "is_today": target_date == today,
        "matches": matches,
    }


def top_daily_scores_with_ties(
    daily_points: Counter[int],
    user_names: dict[int, str],
    user_pictures: dict[int, dict[str, Any]] | None = None,
    limit: int = 5,
) -> list[dict[str, Any]]:
    sorted_scores = [
        (user_id, points)
        for user_id, points in sorted(
            daily_points.items(),
            key=lambda item: (-item[1], normalize_identity(user_names.get(item[0], ""))),
        )
        if points > 0
    ]
    if len(sorted_scores) > limit:
        cutoff_points = sorted_scores[limit - 1][1]
        sorted_scores = [
            (user_id, points) for user_id, points in sorted_scores if points >= cutoff_points
        ]

    ranked_scores = []
    previous_points = None
    current_rank = 0
    for index, (user_id, points) in enumerate(sorted_scores, start=1):
        if points != previous_points:
            current_rank = index
            previous_points = points
        ranked_scores.append(
            {
                "user_id": user_id,
                "rank": current_rank,
                "name": user_names.get(user_id, "Unknown"),
                "points": points,
                "profile_picture": (user_pictures or {}).get(
                    user_id,
                    {
                        "initials": initials(user_names.get(user_id, "Unknown")),
                        "hue": avatar_hue(user_names.get(user_id, "Unknown")),
                    },
                ),
            }
        )
    return ranked_scores


def top_movers_with_ties(
    leaderboard: list[dict[str, Any]],
    limit: int = 5,
) -> list[dict[str, Any]]:
    sorted_movers = sorted(
        [
            row
            for row in leaderboard
            if abs(int(row.get("rank_movement") or 0)) > 0
        ],
        key=lambda row: (
            -abs(int(row.get("rank_movement") or 0)),
            -int(row.get("rank_movement") or 0),
            int(row.get("rank") or 999_999),
            normalize_identity(row.get("name", "")),
        ),
    )
    if len(sorted_movers) > limit:
        cutoff_movement = abs(int(sorted_movers[limit - 1].get("rank_movement") or 0))
        sorted_movers = [
            row
            for row in sorted_movers
            if abs(int(row.get("rank_movement") or 0)) >= cutoff_movement
        ]

    return [
        {
            "user_id": row["user_id"],
            "name": row["name"],
            "rank": row.get("rank"),
            "rank_previous": row.get("rank_previous"),
            "rank_movement": row.get("rank_movement") or 0,
            "profile_picture": row.get("profile_picture"),
        }
        for row in sorted_movers
    ]


def build_daily_recap(
    data: dict[str, Any],
    now: datetime | None = None,
    leaderboard: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    current = now or utc_now()
    today = current.astimezone(AMSTERDAM_TZ).date()
    completed_matches = [
        match
        for match in data["matches"]
        if match_result(match) is not None and local_match_date(match) <= today
    ]
    if not completed_matches:
        return {
            "available": False,
            "title": "Daily recap",
            "body": "De recap verschijnt zodra er gespeelde wedstrijden met uitslagen zijn.",
            "moments": [],
            "top_players": [],
            "top_movers": [],
        }

    target_date = max(local_match_date(match) for match in completed_matches)
    target_matches = [
        match for match in completed_matches if local_match_date(match) == target_date
    ]
    target_ids = {match["id"] for match in target_matches}
    teams = {team["id"]: team for team in data["teams"]}

    with get_db() as conn:
        predictions = execute(conn, "SELECT * FROM match_predictions").fetchall()
        quiz_predictions = execute(conn, "SELECT * FROM quiz_predictions").fetchall()
        users = execute(conn, "SELECT id, name, profile_image_url FROM users").fetchall()
        leeuwtjes = execute(conn, "SELECT user_id, match_id FROM leeuwtje_predictions").fetchall()

    user_names = {user["id"]: user["name"] for user in users}
    user_pictures = {user["id"]: user_profile_picture(user) for user in users}
    leeuwtjes_by_user: dict[int, set[str]] = {}
    for row in leeuwtjes:
        leeuwtjes_by_user.setdefault(row["user_id"], set()).add(row["match_id"])

    daily_points: Counter[int] = Counter()
    matches = {match["id"]: match for match in data["matches"]}
    viewership_winners = quiz_viewership_winners(data, list(quiz_predictions))
    for prediction in predictions:
        if prediction["match_id"] not in target_ids:
            continue
        match = matches.get(prediction["match_id"])
        if not match:
            continue
        base_points, _ = match_prediction_points(prediction, match)
        if prediction["match_id"] in leeuwtjes_by_user.get(prediction["user_id"], set()):
            base_points *= 2
        daily_points[prediction["user_id"]] += base_points

    for quiz_prediction in quiz_predictions:
        if quiz_prediction["match_id"] not in target_ids:
            continue
        match = matches.get(quiz_prediction["match_id"])
        if not match:
            continue
        daily_points[quiz_prediction["user_id"]] += quiz_points_for_prediction(
            match,
            quiz_prediction,
            viewership_winners,
        )

    top_user_id, top_points = (None, 0)
    if daily_points:
        top_user_id, top_points = daily_points.most_common(1)[0]
    top_players = top_daily_scores_with_ties(daily_points, user_names, user_pictures)
    top_movers = top_movers_with_ties(leaderboard or build_leaderboard(data))

    moments = []
    for match in sorted(target_matches, key=match_kickoff):
        moments.append(
            {
                "match_id": match["id"],
                "label": (
                    f"{teams.get(match['home_team_id'], {}).get('name', match['home_team_id'])} "
                    f"{match['home_score']}-{match['away_score']} "
                    f"{teams.get(match['away_team_id'], {}).get('name', match['away_team_id'])}"
                ),
            }
        )

    return {
        "available": True,
        "title": f"Recap {target_date.isoformat()}",
        "body": f"{len(target_matches)} gespeelde wedstrijden verwerkt.",
        "moments": moments,
        "top_player": (
            {"name": user_names.get(top_user_id), "points": top_points}
            if top_user_id is not None
            else None
        ),
        "top_players": top_players,
        "top_movers": top_movers,
    }


def user_pool_state(user: dict[str, Any] | None, data: dict[str, Any]) -> dict[str, Any]:
    now = utc_now()
    prediction_rows = []
    quiz_prediction_rows = []
    leeuwtje_rows = []
    winner_pick = None
    top_scorer_pick = ""
    striker_picks: list[str] = []
    if user:
        with get_db() as conn:
            prediction_rows = execute(
                conn,
                "SELECT match_id, home_score, away_score FROM match_predictions WHERE user_id = ?",
                (user["id"],),
            ).fetchall()
            winner_row = execute(
                conn,
                "SELECT team_id FROM winner_predictions WHERE user_id = ?",
                (user["id"],),
            ).fetchone()
            top_scorer_row = execute(
                conn,
                """
                SELECT player_name, player_name_2, player_name_3,
                       striker_name_1, striker_name_2, striker_name_3,
                       striker_name_4, striker_name_5
                FROM top_scorer_predictions
                WHERE user_id = ?
                """,
                (user["id"],),
            ).fetchone()
            quiz_prediction_rows = execute(
                conn,
                """
                SELECT match_id, answer, viewership_prediction
                FROM quiz_predictions
                WHERE user_id = ?
                """,
                (user["id"],),
            ).fetchall()
            leeuwtje_rows = execute(
                conn,
                "SELECT match_id FROM leeuwtje_predictions WHERE user_id = ?",
                (user["id"],),
            ).fetchall()
        winner_pick = winner_row["team_id"] if winner_row else None
        top_scorer_pick = top_scorer_pick_name(top_scorer_row)
        striker_picks = striker_pick_names(top_scorer_row)

    predictions = {
        row["match_id"]: {"home_score": row["home_score"], "away_score": row["away_score"]}
        for row in prediction_rows
    }
    quiz_predictions = {
        row["match_id"]: {
            "answer": row["answer"] or "",
            "viewership_prediction": row["viewership_prediction"],
        }
        for row in quiz_prediction_rows
    }
    leeuwtje_match_ids = [row["match_id"] for row in leeuwtje_rows]
    group_stage_ids = {match["id"] for match in data["matches"] if match["round"] == "Group Stage"}
    group_stage_predictions = sum(1 for match_id in predictions if match_id in group_stage_ids)
    group_stage_quiz_total = sum(1 for match in data["matches"] if match.get("quiz"))
    group_stage_quiz_predictions = sum(
        1
        for match in data["matches"]
        if match.get("quiz") and quiz_complete(match["quiz"], quiz_predictions.get(match["id"]))
    )
    required_group_id = next(
        (group["id"] for group in data["groups"] if NETHERLANDS_TEAM_ID in group["teams"]),
        None,
    )
    required_group_ids = {
        match["id"]
        for match in data["matches"]
        if match["round"] == "Group Stage" and match.get("group") == required_group_id
    }
    required_group_predictions = sum(
        1 for match_id in predictions if match_id in required_group_ids
    )
    knockout_open = [
        match["id"]
        for match in data["matches"]
        if match["round"] != "Group Stage"
        and match.get("home_team_id")
        and match.get("away_team_id")
    ]
    match_locks = {
        match["id"]: {
            "locked": is_prediction_locked(match, now),
            "kickoff_at": iso_utc(match_kickoff(match)),
            "lock_at": iso_utc(match_lock_time(match)),
        }
        for match in data["matches"]
    }
    leaderboard = build_leaderboard(data)

    return {
        "me": user,
        "predictions": predictions,
        "quiz_predictions": quiz_predictions,
        "leeuwtjes_match_ids": leeuwtje_match_ids,
        "winner_pick": winner_pick,
        "top_scorer_pick": top_scorer_pick or None,
        "striker_picks": striker_picks,
        "top_scorer_picks": striker_picks,
        "leaderboard": leaderboard,
        "badge_catalog": badge_catalog(),
        "notifications": build_notifications(data, predictions, quiz_predictions, now),
        "matchday": build_matchday_summary(data, user["id"] if user else None, now),
        "daily_recap": build_daily_recap(data, now, leaderboard),
        "newsletters": newsletter_articles(),
        "progress": {
            "group_stage_predictions": group_stage_predictions,
            "group_stage_total": len(group_stage_ids),
            "group_stage_quiz_predictions": group_stage_quiz_predictions,
            "group_stage_quiz_total": group_stage_quiz_total,
            "required_group_id": required_group_id,
            "required_group_predictions": required_group_predictions,
            "required_group_total": len(required_group_ids),
            "winner_selected": winner_pick is not None,
            "top_scorer_selected": bool(top_scorer_pick),
            "strikers_selected": len(striker_picks) >= STRIKER_PICK_COUNT,
            "knockout_open_count": len(knockout_open),
            "leeuwtjes_used": len(leeuwtje_match_ids),
            "leeuwtjes_total": LEEUWTJES_LIMIT,
        },
        "locks": {
            "matches": match_locks,
            "winner_locked": is_winner_locked(data, now),
            "winner_lock_at": iso_utc(winner_lock_time(data)),
        },
        "rules": {
            "match_scores": MATCH_SCORE_RULES,
            "group_position": GROUP_POSITION_POINTS,
            "world_cup_winner": WINNER_POINTS,
            "world_cup_top_scorer": TOP_SCORER_POINTS,
            "world_cup_strikers": {
                "count": STRIKER_PICK_COUNT,
                "points_per_goal": STRIKER_GOAL_POINTS,
            },
            "quiz_yes_no": QUIZ_YES_NO_POINTS,
            "quiz_open": QUIZ_OPEN_POINTS,
            "quiz_viewership": QUIZ_VIEWERSHIP_POINTS,
            "leeuwtjes_total": LEEUWTJES_LIMIT,
            "note": (
                "Predictions, quiz answers and Leeuwtjes can be adjusted until one hour "
                "before kickoff."
            ),
        },
    }


def match_result_details(match_id: str, data: dict[str, Any]) -> dict[str, Any] | None:
    match = next((candidate for candidate in data["matches"] if candidate["id"] == match_id), None)
    if match is None:
        return None

    with get_db() as conn:
        result = execute(
            conn,
            """
            SELECT match_id, source, source_fixture_id, status_long, status_short,
                   elapsed, home_score, away_score, synced_at
            FROM match_results
            WHERE match_id = ?
            """,
            (match_id,),
        ).fetchone()
        events = execute(
            conn,
            """
            SELECT elapsed, extra, local_team_id, api_team_id, team_name, api_player_id,
                   player_name, api_assist_id, assist_name, event_type, detail, comments
            FROM match_events
            WHERE match_id = ?
            ORDER BY COALESCE(elapsed, 999), COALESCE(extra, 0), provider_event_key
            """,
            (match_id,),
        ).fetchall()
        clean_sheets = execute(
            conn,
            """
            SELECT local_team_id, api_team_id, team_name
            FROM match_clean_sheets
            WHERE match_id = ?
            ORDER BY team_name
            """,
            (match_id,),
        ).fetchall()
        player_stats = execute(
            conn,
            """
            SELECT local_team_id, api_team_id, team_name, api_player_id, player_name,
                   minutes, position, rating, goals, assists, yellow_cards, red_cards,
                   clean_sheet
            FROM player_match_stats
            WHERE match_id = ?
            ORDER BY team_name, position, player_name
            """,
            (match_id,),
        ).fetchall()

    return {
        "match": match,
        "result": dict(result) if result else None,
        "events": [dict(row) for row in events],
        "clean_sheets": [dict(row) for row in clean_sheets],
        "player_stats": [dict(row) for row in player_stats],
    }


if not CONFIG_ERROR:
    try:
        init_db()
    except Exception:
        if not IS_VERCEL:
            raise
        logger.exception("Database initialization failed")
        CONFIG_ERROR = (
            "Database initialization failed. Check DATABASE_URL or POSTGRES_URL in Vercel."
        )


@app.get("/api/health")
def health():
    if CONFIG_ERROR:
        return jsonify({"ok": False, "database": database_label(), "error": CONFIG_ERROR}), 503
    try:
        with get_db() as conn:
            execute(conn, "SELECT 1").fetchone()
    except Exception:
        logger.exception("Database health check failed")
        return (
            jsonify(
                {
                    "ok": False,
                    "database": database_label(),
                    "error": "Database connection failed.",
                }
            ),
            503,
        )
    return jsonify(
        {
            "ok": True,
            "database": database_label(),
            "schema_version": DB_SCHEMA_VERSION,
            "static_data": static_data_manifest(),
        }
    )


@app.get("/api/world-cup")
def world_cup():
    return jsonify(load_world_cup_data())


@app.get("/api/me")
def me():
    return jsonify({"user": current_user()})


@app.post("/api/auth/login")
def login():
    payload = request.get_json(silent=True) or {}
    name = clean_text(payload.get("name", ""))
    name_key = normalize_identity(name)
    email = normalize_email(payload.get("email", ""))
    raw_password = payload.get("password", "")
    if len(name_key) < 2:
        return jsonify({"error": "Username must be at least 2 characters."}), 400
    if len(name) > 60:
        return jsonify({"error": "Username must be at most 60 characters."}), 400
    if "@" not in email or "." not in email:
        return jsonify({"error": "Use a valid Talpa email address."}), 400

    with get_db() as conn:
        row = execute(
            conn,
            """
            SELECT id, name, email, profile_image_url, password_hash
            FROM users
            WHERE LOWER(TRIM(email)) = ?
            ORDER BY id
            """,
            (email,),
        ).fetchone()
        if row is None:
            try:
                password = validate_password(raw_password)
            except ValueError as error:
                return jsonify({"error": str(error)}), 400
            execute(
                conn,
                "INSERT INTO users (name, email, password_hash) VALUES (?, ?, ?)",
                (name, email, generate_password_hash(password)),
            )
            row = execute(
                conn,
                """
                SELECT id, name, email, profile_image_url, password_hash
                FROM users
                WHERE email = ?
                """,
                (email,),
            ).fetchone()
        elif normalize_identity(row["name"]) != name_key:
            return jsonify({"error": "Use the username linked to this email address."}), 409
        elif not raw_password or not check_password_hash(row["password_hash"], str(raw_password)):
            return jsonify({"error": "Incorrect password."}), 401
        elif row["email"] != email:
            execute(
                conn,
                "UPDATE users SET email = ? WHERE id = ?",
                (email, row["id"]),
            )
            row = execute(
                conn,
                """
                SELECT id, name, email, profile_image_url, password_hash
                FROM users
                WHERE id = ?
                """,
                (row["id"],),
            ).fetchone()

    user = row_to_user(row)
    if user is None:
        logger.error("Failed to load user after login for email %s", email)
        return jsonify({"error": "Could not complete login."}), 500
    session["user_id"] = user["id"]
    logger.info("User %s logged in", user["id"])
    return jsonify({"user": user})


@app.post("/api/auth/forgot-password")
def forgot_password():
    payload = request.get_json(silent=True) or {}
    email = normalize_email(payload.get("email", ""))
    if "@" not in email or "." not in email:
        return jsonify({"error": "Use a valid email address."}), 400

    with get_db() as conn:
        row = execute(
            conn,
            "SELECT id FROM users WHERE LOWER(TRIM(email)) = ? ORDER BY id",
            (email,),
        ).fetchone()
        if row is not None:
            execute(
                conn,
                "UPDATE users SET password_hash = ? WHERE id = ?",
                (generate_password_hash(DEFAULT_PASSWORD), row["id"]),
            )

    if row is not None:
        logger.info("Password reset to default for user %s", row["id"])
    return jsonify(
        {
            "ok": True,
            "message": "If that email belongs to an account, the password is now default-password.",
        }
    )


@app.patch("/api/me/password")
def change_password():
    user, error_response = require_current_user("Log in before changing your password.")
    if error_response:
        return error_response
    assert user is not None

    payload = request.get_json(silent=True) or {}
    current_password = str(payload.get("current_password", ""))
    new_password = payload.get("password", "")
    confirm_password = payload.get("confirm_password", "")
    if str(new_password) != str(confirm_password):
        return jsonify({"error": "Passwords do not match."}), 400
    try:
        validated_password = validate_password(new_password)
    except ValueError as error:
        return jsonify({"error": str(error)}), 400

    with get_db() as conn:
        row = execute(
            conn,
            "SELECT id, password_hash FROM users WHERE id = ?",
            (user["id"],),
        ).fetchone()
        if row is None:
            return jsonify({"error": "Account not found."}), 404
        if not check_password_hash(row["password_hash"], current_password):
            return jsonify({"error": "Current password is incorrect."}), 401
        execute(
            conn,
            "UPDATE users SET password_hash = ? WHERE id = ?",
            (generate_password_hash(validated_password), user["id"]),
        )

    logger.info("User %s changed password", user["id"])
    return jsonify({"ok": True})


@app.patch("/api/me")
def update_me():
    user, error_response = require_current_user("Log in before changing your profile.")
    if error_response:
        return error_response
    assert user is not None

    payload = request.get_json(silent=True) or {}
    has_name = "name" in payload
    has_profile_image = "profile_image_url" in payload
    if not has_name and not has_profile_image:
        return jsonify({"error": "No profile changes submitted."}), 400

    name = clean_text(payload.get("name", user["name"]))
    if has_name:
        if len(normalize_identity(name)) < 2:
            return jsonify({"error": "Username must be at least 2 characters."}), 400
        if len(name) > 60:
            return jsonify({"error": "Username must be at most 60 characters."}), 400

    try:
        profile_image_url = (
            validate_profile_image_url(payload.get("profile_image_url"))
            if has_profile_image
            else row_value(user, "profile_picture", {}).get("image_url")
        )
    except ValueError as error:
        return jsonify({"error": str(error)}), 400

    with get_db() as conn:
        if has_name and has_profile_image:
            execute(
                conn,
                "UPDATE users SET name = ?, profile_image_url = ? WHERE id = ?",
                (name, profile_image_url, user["id"]),
            )
        elif has_name:
            execute(conn, "UPDATE users SET name = ? WHERE id = ?", (name, user["id"]))
        else:
            execute(
                conn,
                "UPDATE users SET profile_image_url = ? WHERE id = ?",
                (profile_image_url, user["id"]),
            )
        row = execute(
            conn,
            "SELECT id, name, email, profile_image_url FROM users WHERE id = ?",
            (user["id"],),
        ).fetchone()

    updated_user = row_to_user(row)
    if updated_user is None:
        return jsonify({"error": "Could not update your username."}), 500
    logger.info("User %s updated profile", updated_user["id"])
    data = load_world_cup_data()
    return jsonify(user_pool_state(updated_user, data))


@app.post("/api/auth/logout")
def logout():
    user_id = session.get("user_id")
    session.clear()
    if user_id:
        logger.info("User %s logged out", user_id)
    return jsonify({"ok": True})


@app.get("/api/pool")
def pool():
    data = load_world_cup_data()
    return jsonify(user_pool_state(current_user(), data))


@app.get("/api/newsletters")
def newsletters_api():
    return jsonify(
        {
            "articles": newsletter_articles(),
            "max_articles": NEWSLETTER_MAX_ARTICLES,
        }
    )


@app.post("/api/admin/newsletters/refresh")
def newsletters_admin_refresh():
    token_error = require_sync_token()
    if token_error:
        return token_error
    result = run_newsletter_refresh()
    status_code = 200 if result.get("ok") else 503
    return jsonify(result), status_code


@app.get("/api/matches/<match_id>/result")
def match_result_api(match_id: str):
    user, error_response = require_current_user()
    if error_response:
        return error_response
    data = load_world_cup_data()
    details = match_result_details(match_id, data)
    if details is None:
        return jsonify({"error": "Match not found."}), 404
    return jsonify(details)


@app.get("/api/admin/api-football/status")
def api_football_admin_status():
    token_error = require_sync_token()
    if token_error:
        return token_error
    return jsonify(api_football_status())


@app.post("/api/admin/api-football/sync")
def api_football_admin_sync():
    token_error = require_sync_token()
    if token_error:
        return token_error
    payload = request.get_json(silent=True) or {}
    data = load_world_cup_data()
    try:
        result = run_api_football_completed_sync(
            data,
            force=bool(payload.get("force", False)),
            dry_run=bool(payload.get("dry_run", False)),
            limit=int(payload.get("limit", API_FOOTBALL_MAX_BATCH_SIZE)),
        )
    except Exception as error:
        logger.exception("API-Football manual sync failed")
        result = {
            "ok": False,
            "error": str(error),
            "requests_today": api_football_request_count_today(),
            "daily_limit": API_FOOTBALL_DAILY_LIMIT,
        }
    status_code = 200 if result.get("ok") else 503
    return jsonify(result), status_code


@app.post("/api/admin/api-football/squads/sync")
def api_football_admin_squad_sync():
    token_error = require_sync_token()
    if token_error:
        return token_error
    payload = request.get_json(silent=True) or {}
    data = load_world_cup_data()
    try:
        result = run_api_football_squad_sync(
            data,
            force=bool(payload.get("force", False)),
            dry_run=bool(payload.get("dry_run", False)),
            limit=int(payload.get("limit", API_FOOTBALL_SQUAD_SYNC_BATCH_SIZE)),
        )
    except Exception as error:
        logger.exception("API-Football squad sync failed")
        result = {
            "ok": False,
            "error": str(error),
            "requests_today": api_football_request_count_today(),
            "daily_limit": API_FOOTBALL_DAILY_LIMIT,
        }
    status_code = 200 if result.get("ok") else 503
    return jsonify(result), status_code


@app.get("/api/admin/database/status")
def database_admin_status():
    token_error = require_sync_token()
    if token_error:
        return token_error
    return jsonify(database_snapshot(include_rows=False))


@app.get("/api/admin/database/backup")
def database_admin_backup():
    token_error = require_sync_token()
    if token_error:
        return token_error
    snapshot = database_snapshot(include_rows=True)
    response = jsonify(snapshot)
    filename_time = utc_now().strftime("%Y%m%dT%H%M%SZ")
    response.headers["Content-Disposition"] = (
        f'attachment; filename="wk-hub-backup-{filename_time}.json"'
    )
    return response


@app.get("/api/cron/api-football-sync")
def api_football_cron_sync():
    token_error = require_sync_token()
    if token_error:
        return token_error
    data = load_world_cup_data()
    try:
        result = run_api_football_completed_sync(data)
    except Exception as error:
        logger.exception("API-Football cron sync failed")
        result = {
            "ok": False,
            "error": str(error),
            "requests_today": api_football_request_count_today(),
            "daily_limit": API_FOOTBALL_DAILY_LIMIT,
        }
    status_code = 200 if result.get("ok") else 503
    return jsonify(result), status_code


@app.get("/api/cron/api-football-squad-sync")
def api_football_squad_cron_sync():
    token_error = require_sync_token()
    if token_error:
        return token_error
    data = load_world_cup_data()
    try:
        result = run_api_football_squad_sync(data)
    except Exception as error:
        logger.exception("API-Football squad cron sync failed")
        result = {
            "ok": False,
            "error": str(error),
            "requests_today": api_football_request_count_today(),
            "daily_limit": API_FOOTBALL_DAILY_LIMIT,
        }
    status_code = 200 if result.get("ok") else 503
    return jsonify(result), status_code


@app.get("/api/social")
def social():
    user, error_response = require_current_user()
    if error_response:
        return error_response
    assert user is not None
    return jsonify(social_state(user))


@app.post("/api/social/follow")
def follow_user():
    user, error_response = require_current_user()
    if error_response:
        return error_response
    assert user is not None

    payload = request.get_json(silent=True) or {}
    raw_followed_id = payload.get("user_id")
    if raw_followed_id is None:
        return jsonify({"error": "Choose a player to follow."}), 400
    try:
        followed_id = int(raw_followed_id)
    except (TypeError, ValueError):
        return jsonify({"error": "Choose a player to follow."}), 400
    if followed_id == user["id"]:
        return jsonify({"error": "You cannot follow yourself."}), 400

    with get_db() as conn:
        target = execute(conn, "SELECT id FROM users WHERE id = ?", (followed_id,)).fetchone()
        if target is None:
            return jsonify({"error": "That player is not in the pool."}), 404
        execute(
            conn,
            """
            INSERT INTO user_follows (follower_id, followed_id, created_at)
            VALUES (?, ?, CURRENT_TIMESTAMP)
            ON CONFLICT(follower_id, followed_id) DO NOTHING
            """,
            (user["id"], followed_id),
        )

    return jsonify(social_state(user))


@app.delete("/api/social/follow/<int:followed_id>")
def unfollow_user(followed_id: int):
    user, error_response = require_current_user()
    if error_response:
        return error_response
    assert user is not None

    with get_db() as conn:
        execute(
            conn,
            "DELETE FROM user_follows WHERE follower_id = ? AND followed_id = ?",
            (user["id"], followed_id),
        )

    return jsonify(social_state(user))


@app.get("/api/profiles/<int:profile_user_id>/predictions")
def profile_predictions(profile_user_id: int):
    user, error_response = require_current_user()
    if error_response:
        return error_response
    assert user is not None

    with get_db() as conn:
        profile = execute(
            conn,
            "SELECT id, name FROM users WHERE id = ?",
            (profile_user_id,),
        ).fetchone()
    if profile is None:
        return jsonify({"error": "Player profile not found."}), 404

    data = load_world_cup_data()
    include_unplayed = profile_user_id == user["id"]
    return jsonify(
        {
            "user_id": profile_user_id,
            "name": profile["name"],
            "limited_to_completed_matches": not include_unplayed,
            "groups": user_prediction_groups(profile_user_id, data, include_unplayed),
        }
    )


@app.post("/api/predictions")
def save_predictions():
    user, error_response = require_current_user("Log in before saving predictions.")
    if error_response:
        logger.warning("Rejected prediction save without authenticated session")
        return error_response
    assert user is not None

    data = load_world_cup_data()
    matches = {match["id"]: match for match in data["matches"]}
    allowed_match_ids = {
        match["id"]
        for match in data["matches"]
        if match["round"] == "Group Stage"
        or (match.get("home_team_id") and match.get("away_team_id"))
    }
    team_ids = {team["id"] for team in data["teams"]}
    payload = request.get_json(silent=True) or {}
    prediction_items = payload.get("predictions", [])
    quiz_items = payload.get("quiz_predictions")
    leeuwtje_items = payload.get("leeuwtjes_match_ids")
    winner_team_id = payload.get("winner_team_id")
    top_scorer_submitted = (
        "top_scorer_name" in payload or "top_scorer_names" in payload
    )
    raw_top_scorer = payload.get("top_scorer_name")
    raw_legacy_top_scorers = payload.get("top_scorer_names")
    if raw_top_scorer is None and isinstance(raw_legacy_top_scorers, list):
        raw_top_scorer = raw_legacy_top_scorers[0] if raw_legacy_top_scorers else ""
    strikers_submitted = "striker_names" in payload or "top_scorer_names" in payload
    raw_strikers = payload.get("striker_names")
    if raw_strikers is None and isinstance(raw_legacy_top_scorers, list):
        raw_strikers = raw_legacy_top_scorers[:STRIKER_PICK_COUNT]
    now = utc_now()

    if not isinstance(prediction_items, list):
        return jsonify({"error": "Predictions must be a list."}), 400
    if quiz_items is not None and not isinstance(quiz_items, list):
        return jsonify({"error": "Quiz predictions must be a list."}), 400
    if leeuwtje_items is not None and not isinstance(leeuwtje_items, list):
        return jsonify({"error": "Leeuwtjes must be a list."}), 400
    if raw_legacy_top_scorers is not None and not isinstance(raw_legacy_top_scorers, list):
        return jsonify({"error": "Top scorer picks must be a list."}), 400
    if raw_strikers is not None and not isinstance(raw_strikers, list):
        return jsonify({"error": "Striker picks must be a list."}), 400

    with get_db() as conn:
        existing_predictions = {
            row["match_id"]: row
            for row in execute(
                conn,
                "SELECT match_id, home_score, away_score FROM match_predictions WHERE user_id = ?",
                (user["id"],),
            ).fetchall()
        }
        existing_winner = execute(
            conn,
            "SELECT team_id FROM winner_predictions WHERE user_id = ?",
            (user["id"],),
        ).fetchone()
        existing_top_scorer = execute(
            conn,
            """
            SELECT player_name, player_name_2, player_name_3,
                   striker_name_1, striker_name_2, striker_name_3,
                   striker_name_4, striker_name_5
            FROM top_scorer_predictions
            WHERE user_id = ?
            """,
            (user["id"],),
        ).fetchone()
        existing_quizzes = {
            row["match_id"]: row
            for row in execute(
                conn,
                """
                SELECT match_id, answer, viewership_prediction
                FROM quiz_predictions
                WHERE user_id = ?
                """,
                (user["id"],),
            ).fetchall()
        }
        existing_leeuwtjes = {
            row["match_id"]
            for row in execute(
                conn,
                "SELECT match_id FROM leeuwtje_predictions WHERE user_id = ?",
                (user["id"],),
            ).fetchall()
        }

    cleaned = []
    for item in prediction_items:
        match_id = str(item.get("match_id", ""))
        if match_id not in allowed_match_ids:
            return jsonify({"error": f"Match {match_id} is not open for predictions."}), 400
        try:
            home_score = int(item.get("home_score"))
            away_score = int(item.get("away_score"))
        except (TypeError, ValueError):
            return jsonify({"error": "Scores must be whole numbers."}), 400
        if home_score < 0 or away_score < 0 or home_score > 30 or away_score > 30:
            return jsonify({"error": "Scores must be between 0 and 30."}), 400
        if is_prediction_locked(matches[match_id], now):
            existing = existing_predictions.get(match_id)
            existing_matches_submission = (
                existing
                and existing["home_score"] == home_score
                and existing["away_score"] == away_score
            )
            if existing_matches_submission:
                continue
            return jsonify({"error": f"Predictions for match {match_id} are closed."}), 400
        cleaned.append((user["id"], match_id, home_score, away_score))

    cleaned_quizzes = []
    quiz_deletes = []
    if quiz_items is not None:
        for item in quiz_items:
            match_id = str(item.get("match_id", ""))
            match = matches.get(match_id)
            if match_id not in allowed_match_ids or match is None or not match.get("quiz"):
                return jsonify({"error": f"Quiz for match {match_id} is not available."}), 400
            quiz = match["quiz"]
            answer = clean_text(item.get("answer", ""))
            if len(answer) > 160:
                return jsonify({"error": "Quiz answers can be at most 160 characters."}), 400
            choices = {normalize_answer(choice) for choice in quiz.get("choices", [])}
            if answer and choices and normalize_answer(answer) not in choices:
                return jsonify({"error": f"Choose a valid quiz answer for match {match_id}."}), 400

            viewership_prediction = item.get("viewership_prediction")
            if viewership_prediction in ("", None):
                viewership_prediction = None
            else:
                try:
                    viewership_prediction = int(viewership_prediction)
                except (TypeError, ValueError):
                    return jsonify({"error": "Kijkcijfers must be a whole number."}), 400
                if viewership_prediction < 0 or viewership_prediction > 50_000_000:
                    return jsonify({"error": "Kijkcijfers must be between 0 and 50,000,000."}), 400
            if viewership_prediction is not None and not quiz.get("viewership"):
                return jsonify({"error": f"Match {match_id} has no kijkcijfers question."}), 400

            existing = existing_quizzes.get(match_id)
            existing_answer = clean_text(existing["answer"] if existing else "")
            existing_viewership = existing["viewership_prediction"] if existing else None
            changed = answer != existing_answer or viewership_prediction != existing_viewership
            if changed and is_prediction_locked(match, now):
                return jsonify({"error": f"Quiz for match {match_id} is closed."}), 400
            if answer or viewership_prediction is not None:
                cleaned_quizzes.append((user["id"], match_id, answer, viewership_prediction))
            elif existing:
                quiz_deletes.append((user["id"], match_id))

    submitted_leeuwtjes: set[str] | None = None
    if leeuwtje_items is not None:
        submitted_leeuwtjes = {str(match_id) for match_id in leeuwtje_items}
        if len(submitted_leeuwtjes) > LEEUWTJES_LIMIT:
            return jsonify({"error": f"You can use at most {LEEUWTJES_LIMIT} Leeuwtjes."}), 400
        invalid_leeuwtjes = submitted_leeuwtjes - allowed_match_ids
        if invalid_leeuwtjes:
            return jsonify({"error": "Leeuwtjes can only be used on prediction matches."}), 400
        changed_leeuwtjes = submitted_leeuwtjes ^ existing_leeuwtjes
        locked_leeuwtjes = [
            match_id
            for match_id in changed_leeuwtjes
            if is_prediction_locked(matches[match_id], now)
        ]
        if locked_leeuwtjes:
            return jsonify({"error": "Leeuwtjes for locked matches cannot be changed."}), 400

    if winner_team_id and winner_team_id not in team_ids:
        return jsonify({"error": "Winner pick must be one of the participating teams."}), 400
    winner_change_locked = (
        winner_team_id
        and is_winner_locked(data, now)
        and (not existing_winner or existing_winner["team_id"] != winner_team_id)
    )
    if winner_change_locked:
        return jsonify({"error": "The tournament winner pick is closed."}), 400
    top_scorer_name: str | None = None
    if top_scorer_submitted:
        top_scorer_name = clean_text(raw_top_scorer)
        if len(top_scorer_name) > 120:
            return jsonify({"error": "Top scorer name must be at most 120 characters."}), 400

    striker_names: list[str] | None = None
    if strikers_submitted:
        if raw_strikers and len(raw_strikers) > STRIKER_PICK_COUNT:
            return jsonify({"error": f"Choose at most {STRIKER_PICK_COUNT} strikers."}), 400
        striker_names = [clean_text(name) for name in (raw_strikers or [])]
        striker_names = [name for name in striker_names if name]
        if any(len(name) > 120 for name in striker_names):
            return jsonify({"error": "Striker names must be at most 120 characters."}), 400
        normalized_strikers = [normalized_player_name(name) for name in striker_names]
        if len(set(normalized_strikers)) != len(normalized_strikers):
            return jsonify({"error": "Choose five different strikers."}), 400

    existing_top_scorer_name = top_scorer_pick_name(existing_top_scorer)
    existing_striker_names = striker_pick_names(existing_top_scorer)
    top_scorer_changed = top_scorer_submitted and top_scorer_name != existing_top_scorer_name
    strikers_changed = strikers_submitted and striker_names != existing_striker_names
    if (top_scorer_changed or strikers_changed) and is_winner_locked(data, now):
        return jsonify({"error": "The top scorer and striker picks are closed."}), 400

    audit_payload = {
        "predictions": [
            {"match_id": match_id, "home_score": home_score, "away_score": away_score}
            for _, match_id, home_score, away_score in cleaned
        ],
        "quiz_predictions": [
            {
                "match_id": match_id,
                "answer": answer,
                "viewership_prediction": viewership_prediction,
            }
            for _, match_id, answer, viewership_prediction in cleaned_quizzes
        ],
        "quiz_deletes": [match_id for _, match_id in quiz_deletes],
        "leeuwtjes_match_ids": (
            sorted(submitted_leeuwtjes) if submitted_leeuwtjes is not None else None
        ),
        "winner_team_id": winner_team_id or None,
        "top_scorer_name": top_scorer_name if top_scorer_submitted else None,
        "striker_names": striker_names if strikers_submitted else None,
    }

    with get_db() as conn:
        execute(
            conn,
            """
            INSERT INTO prediction_audit_log (user_id, action, payload_json, created_at)
            VALUES (?, ?, ?, CURRENT_TIMESTAMP)
            """,
            (
                user["id"],
                "save_predictions",
                json.dumps(audit_payload, ensure_ascii=False, sort_keys=True),
            ),
        )
        for prediction_row in cleaned:
            execute(
                conn,
                """
                INSERT INTO match_predictions (
                    user_id, match_id, home_score, away_score, updated_at
                )
                VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
                ON CONFLICT(user_id, match_id)
                DO UPDATE SET home_score = excluded.home_score,
                              away_score = excluded.away_score,
                              updated_at = CURRENT_TIMESTAMP
                """,
                prediction_row,
            )
        for quiz_row in cleaned_quizzes:
            execute(
                conn,
                """
                INSERT INTO quiz_predictions (
                    user_id, match_id, answer, viewership_prediction, updated_at
                )
                VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
                ON CONFLICT(user_id, match_id)
                DO UPDATE SET answer = excluded.answer,
                              viewership_prediction = excluded.viewership_prediction,
                              updated_at = CURRENT_TIMESTAMP
                """,
                quiz_row,
            )
        for quiz_delete in quiz_deletes:
            execute(
                conn,
                "DELETE FROM quiz_predictions WHERE user_id = ? AND match_id = ?",
                quiz_delete,
            )
        if submitted_leeuwtjes is not None:
            execute(conn, "DELETE FROM leeuwtje_predictions WHERE user_id = ?", (user["id"],))
            for match_id in sorted(submitted_leeuwtjes):
                execute(
                    conn,
                    """
                    INSERT INTO leeuwtje_predictions (user_id, match_id, updated_at)
                    VALUES (?, ?, CURRENT_TIMESTAMP)
                    """,
                    (user["id"], match_id),
                )
        if winner_team_id:
            execute(
                conn,
                """
                INSERT INTO winner_predictions (user_id, team_id, updated_at)
                VALUES (?, ?, CURRENT_TIMESTAMP)
                ON CONFLICT(user_id)
                DO UPDATE SET team_id = excluded.team_id,
                              updated_at = CURRENT_TIMESTAMP
                """,
                (user["id"], winner_team_id),
            )
        if top_scorer_submitted or strikers_submitted:
            stored_top_scorer_name = (
                top_scorer_name if top_scorer_submitted else existing_top_scorer_name
            )
            stored_striker_names = (
                striker_names if strikers_submitted else existing_striker_names
            )
            if stored_top_scorer_name:
                padded_strikers = [*(stored_striker_names or []), None, None, None, None, None]
                execute(
                    conn,
                    """
                    INSERT INTO top_scorer_predictions (
                        user_id, player_name, player_name_2, player_name_3,
                        striker_name_1, striker_name_2, striker_name_3,
                        striker_name_4, striker_name_5, updated_at
                    )
                    VALUES (?, ?, NULL, NULL, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                    ON CONFLICT(user_id)
                    DO UPDATE SET player_name = excluded.player_name,
                                  player_name_2 = NULL,
                                  player_name_3 = NULL,
                                  striker_name_1 = excluded.striker_name_1,
                                  striker_name_2 = excluded.striker_name_2,
                                  striker_name_3 = excluded.striker_name_3,
                                  striker_name_4 = excluded.striker_name_4,
                                  striker_name_5 = excluded.striker_name_5,
                                  updated_at = CURRENT_TIMESTAMP
                    """,
                    (
                        user["id"],
                        stored_top_scorer_name,
                        padded_strikers[0],
                        padded_strikers[1],
                        padded_strikers[2],
                        padded_strikers[3],
                        padded_strikers[4],
                    ),
                )
            else:
                execute(
                    conn,
                    "DELETE FROM top_scorer_predictions WHERE user_id = ?",
                    (user["id"],),
                )

    logger.info(
        (
            "Saved %s match predictions, %s quiz answers, winner=%s, "
            "top_scorer=%s and strikers=%s for user %s"
        ),
        len(cleaned),
        len(cleaned_quizzes),
        bool(winner_team_id),
        bool(top_scorer_name),
        bool(striker_names),
        user["id"],
    )
    return jsonify(user_pool_state(user, data))


@app.get("/api/cron/newsletters-refresh")
def newsletters_cron_refresh():
    token_error = require_sync_token()
    if token_error:
        return token_error
    try:
        result = run_newsletter_refresh()
    except Exception as error:
        logger.exception("Newsletter cron refresh failed")
        result = {"ok": False, "error": str(error), "articles": []}
    status_code = 200 if result.get("ok") else 503
    return jsonify(result), status_code


@app.get("/")
def index():
    return send_from_directory(DIST_DIR, "index.html")


@app.get("/<path:path>")
def frontend(path: str):
    if path.startswith("api/"):
        abort(404)
    target = DIST_DIR / path
    if target.is_file():
        return send_from_directory(DIST_DIR, path)
    return send_from_directory(DIST_DIR, "index.html")


@app.errorhandler(404)
def fallback_to_frontend(error: Any):
    if request.method == "GET" and not request.path.startswith("/api/"):
        return send_from_directory(DIST_DIR, "index.html")
    return jsonify({"error": "Not found"}), 404


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=8000, debug=False)
