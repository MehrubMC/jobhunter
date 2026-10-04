"""
Discord New-Grad SWE Job Alert Bot
==================================
Every hour this bot:
  1. Scrapes four GitHub job-list repos (Markdown / HTML tables).
  2. Pulls LinkedIn + Indeed listings through JobSpy.
  3. Sorts jobs into three categories and filters them:
       SWE = new-grad software roles, EE = electrical/hardware/embedded internships,
       IE  = industrial / process / manufacturing / supply-chain internships
             (Atlanta or New York).
  4. Skips anything already stored in SQLite.
  5. Posts new jobs as embeds in one Discord channel. Each category's owner is
     pinged once per hourly run, followed by all of that category's new jobs.

Configuration comes from environment variables (see .env.example).
"""
from __future__ import annotations

import asyncio
import hashlib
import html
import logging
import os
import random
import re
import sqlite3
import sys
import threading
import time
from collections import Counter
from dataclasses import dataclass, field
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

import discord
import requests
from discord.ext import tasks
from dotenv import load_dotenv
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

load_dotenv()
log = logging.getLogger("jobbot")

# --------------------------------------------------------------------------- #
# Discord users to ping, per job category
# --------------------------------------------------------------------------- #
SWE_USER_ID = "454437405987045396"
EE_USER_ID = "490315556252024835"
IE_USER_ID = "219949510611304450"
CATEGORY_PING_IDS = {"SWE": SWE_USER_ID, "EE": EE_USER_ID, "IE": IE_USER_ID}

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #
DB_PATH = os.getenv("DB_PATH", "jobs.db")
MAX_PER_CYCLE = int(os.getenv("MAX_PER_CYCLE", "25"))            # jobs per category, per hourly run
# EE / IE internships are often on-site elsewhere. Set either to "false" to drop the
# location requirement for that category only. (Defaults: EE = New York / Hybrid /
# Remote; IE = Atlanta / New York / Hybrid / Remote.)
EE_REQUIRE_LOCATION = os.getenv("EE_REQUIRE_LOCATION", "true").lower() == "true"
IE_REQUIRE_LOCATION = os.getenv("IE_REQUIRE_LOCATION", "true").lower() == "true"
SEED_ON_FIRST_RUN = os.getenv("SEED_ON_FIRST_RUN", "true").lower() == "true"
ENABLE_JOBSPY = os.getenv("ENABLE_JOBSPY", "true").lower() == "true"
# LOW_POWER_MODE=true makes the bot gentle for hosts that stop servers over CPU use:
# few searches per run, small pages, long pauses. Normal mode is the default. Any of
# these can still be set individually in .env and wins over the mode.
LOW_POWER = os.getenv("LOW_POWER_MODE", "false").lower() == "true"


def _setting(name: str, normal, low) -> str:
    return os.getenv(name, str(low if LOW_POWER else normal))


JOBSPY_RESULTS = int(_setting("JOBSPY_RESULTS", 25, 10))             # per site, per query
JOBSPY_HOURS_OLD = int(os.getenv("JOBSPY_HOURS_OLD", "72"))
# Max seconds JobSpy may spend per hourly run. Searches not reached this run are
# picked up first on the next run, so every search still gets covered over time.
JOBSPY_TIME_BUDGET = int(os.getenv("JOBSPY_TIME_BUDGET_SECONDS", "600"))
JOBSPY_MAX_SEARCHES = int(_setting("JOBSPY_MAX_SEARCHES_PER_CYCLE", 999, 8))   # 999 = all
JOBSPY_DELAY = float(_setting("JOBSPY_DELAY_SECONDS", 5, 10))        # pause after each search
GITHUB_PAUSE = float(_setting("GITHUB_PAUSE_SECONDS", 0.2, 1.0))     # between GitHub lists
STARTUP_DELAY = int(_setting("STARTUP_DELAY_SECONDS", 5, 20))        # settle time at startup
JOBSPY_SITES = [x.strip() for x in os.getenv("JOBSPY_SITES", "linkedin,indeed").split(",") if x.strip()]
PROXIES = [p.strip() for p in os.getenv("PROXIES", "").split(",") if p.strip()]

REPO_SOURCES = {
    "GitHub · speedyapply/2027-SWE-College-Jobs (USA)":
        "https://raw.githubusercontent.com/speedyapply/2027-SWE-College-Jobs/main/NEW_GRAD_USA.md",
    "GitHub · speedyapply/2027-SWE-College-Jobs (Intl)":
        "https://raw.githubusercontent.com/speedyapply/2027-SWE-College-Jobs/main/NEW_GRAD_INTL.md",
    "GitHub · SimplifyJobs/New-Grad-Positions":
        "https://raw.githubusercontent.com/SimplifyJobs/New-Grad-Positions/dev/README.md",
    "GitHub · zapplyjobs/New-Grad-Software-Engineering-Jobs-2027":
        "https://raw.githubusercontent.com/zapplyjobs/New-Grad-Software-Engineering-Jobs-2027/main/README.md",
    "GitHub · SimplifyJobs/Summer2027-Internships":
        "https://raw.githubusercontent.com/SimplifyJobs/Summer2027-Internships/dev/README.md",
    "GitHub · SimplifyJobs/Summer2027-Internships (Off-Season)":
        "https://raw.githubusercontent.com/SimplifyJobs/Summer2027-Internships/dev/README-Off-Season.md",
}
# Internship lists feed the EE and IE categories only. Everything else is a new-grad list.
INTERN_SOURCES = {
    "GitHub · SimplifyJobs/Summer2027-Internships",
    "GitHub · SimplifyJobs/Summer2027-Internships (Off-Season)",
}
NEW_GRAD_SOURCES = set(REPO_SOURCES) - INTERN_SOURCES

SWE_TERMS = [
    "new grad software engineer 2027",
    "entry level frontend engineer react typescript",
    "early career software engineer javascript",
]
EE_TERMS = [
    "electrical engineering intern",
    "hardware engineering intern",
    "embedded systems intern",
]
IE_TERMS = [
    "process engineer intern",
    "solutions engineer intern",
    "continuous improvement engineer intern",
    "manufacturing engineer intern",
    "industrial engineer intern",
    "supply chain intern",
]
JOBSPY_TERMS = SWE_TERMS + EE_TERMS + IE_TERMS

# (search term, location) pairs. Remote searches put "remote" in the term because
# Indeed doesn't allow combining is_remote with hours_old. IE terms also get an
# Atlanta search.
# Atlanta goes first so the IE searches run in the very first cycle rather than the fourth.
JOBSPY_SEARCHES = (
    [(t, "Atlanta, GA") for t in IE_TERMS]
    + [(t, "New York, NY") for t in JOBSPY_TERMS]
    + [(f"remote {t}", "United States") for t in JOBSPY_TERMS]
)

# --------------------------------------------------------------------------- #
# Filters
# --------------------------------------------------------------------------- #
# --- SWE: new grad / 2027 / entry level software roles ---
ROLE_RE = re.compile(
    r"\b(2027|new[- ]?grad(uate)?s?|early[- ]career|entry[- ]level)\b", re.I
)
STACK_RE = re.compile(
    r"\b(react(\.?js)?|typescript|javascript|front[- ]?end|next\.?js|ui engineer)\b|\bjs\b|\bts\b",
    re.I,
)
SWE_TITLE_RE = re.compile(
    r"software|developer|front[- ]?end|full[- ]?stack|\bswe\b|web\s+(developer|engineer)|ui engineer",
    re.I,
)
# SWE titles must NOT look senior or like an internship / co-op.
SWE_EXCLUDE_RE = re.compile(
    r"\b(senior|sr|staff|principal|lead|manager|director|architect|intern(ship)?|co-?op|ii|iii|iv)\b|head of",
    re.I,
)
# Mid-level titles that need years of experience: "Software Engineer 4", "SDE 2",
# "Engineer V", "Level 3". The number has to sit right after a job word, so years
# ("Software Engineer 2027"), versions ("Python 3") and "3D" are not caught, and
# level I / 1 (entry level) is kept. Roman II-IV are already caught by the regex above.
SWE_LEVEL_RE = re.compile(
    r"\b(engineer|engineering|developer|swe|sde|sdet|programmer)\b[\s,:()/\-–]*(v|vi|[2-9])\b(?!\.\d)"
    r"|\blevel\s*([2-9]|ii|iii|iv|v)\b",
    re.I,
)

# --- Internship categories (EE and IE share the intern requirement) ---
EE_TITLE_RE = re.compile(r"electrical|hardware|embedded|electronics?", re.I)
# No trailing \b on "engineer" so "Process Engineering Intern" matches too.
IE_TITLE_RE = re.compile(
    r"process\s+engineer|solutions?\s+engineer|continuous[- ]improvement.{0,20}engineer"
    r"|manufacturing\s+engineer|industrial\s+engineer|supply[- ]chain",
    re.I,
)
INTERN_RE = re.compile(r"\b(intern(ship)?s?|co-?op)\b", re.I)
# Seniority words only. "intern" is required for these, so it isn't excluded here.
INTERN_EXCLUDE_RE = re.compile(
    r"\b(senior|sr|staff|principal|lead|manager|director|architect|iii|iv)\b|head of", re.I
)
# Tells which JobSpy queries were EE/IE searches, so their stray results
# can't sneak into the SWE category.
NON_SWE_QUERY_RE = re.compile(
    r"electrical|hardware|embedded|electronics|process engineer|solutions engineer|continuous improvement"
    r"|manufacturing engineer|industrial engineer|supply chain",
    re.I,
)

LOCATION_RE = re.compile(
    r"new york|\bnyc\b|\bny\b|brooklyn|manhattan|hybrid|remote", re.I
)
# IE also accepts Atlanta. "GA" catches suburbs (Alpharetta, Marietta...) but also
# the rest of Georgia (Savannah, Augusta).
IE_LOCATION_RE = re.compile(LOCATION_RE.pattern + r"|atlanta|\bga\b", re.I)


@dataclass
class Job:
    company: str
    title: str
    location: str
    url: str
    source: str
    description: str = ""
    from_jobspy: bool = False
    search_term: str = ""        # JobSpy query that found this job
    salary: str = ""             # pay text if the source gives one, e.g. "$186k/yr"
    category: str = ""           # "SWE", "EE" or "IE", set by passes_filters()
    stack_match: bool = False
    url_key: str = field(init=False)
    fingerprint: str = field(init=False)

    def __post_init__(self) -> None:
        self.url_key = normalize_url(self.url)
        # Company + title only, so the same posting listed in several repos
        # (with different URLs and location spellings) is treated as one job.
        raw = f"{self.company}|{self.title}".lower()
        self.fingerprint = hashlib.sha1(re.sub(r"[^a-z0-9|]+", "", raw).encode()).hexdigest()


def _matches_swe(job: Job) -> bool:
    """New-grad / 2027 / entry-level software roles (never internships)."""
    if job.source in INTERN_SOURCES:                      # internship lists are EE-only
        return False
    if job.from_jobspy and NON_SWE_QUERY_RE.search(job.search_term):
        return False                                      # result of an EE/IE search
    if not SWE_TITLE_RE.search(job.title):
        return False
    if SWE_EXCLUDE_RE.search(job.title) or SWE_LEVEL_RE.search(job.title):
        return False
    text = f"{job.title} {job.description}"
    if job.source in NEW_GRAD_SOURCES:
        pass                                              # the list itself is new-grad only
    elif job.description:
        if not ROLE_RE.search(text):
            return False
    # JobSpy result with no description (LinkedIn): the SWE search terms already
    # targeted new-grad roles, and senior titles were excluded above.
    job.stack_match = bool(STACK_RE.search(text))
    return True


def _matches_internship(job: Job, title_re: re.Pattern) -> bool:
    """Title matches the category AND the title/description says intern / co-op."""
    if not title_re.search(job.title) or INTERN_EXCLUDE_RE.search(job.title):
        return False
    return bool(INTERN_RE.search(f"{job.title} {job.description}"))


def passes_filters(job: Job) -> bool:
    """Assigns job.category ("SWE", "EE" or "IE") and returns True if it matches one."""
    place = f"{job.location} {job.title}"
    location_ok = bool(LOCATION_RE.search(place))
    ie_location_ok = bool(IE_LOCATION_RE.search(place))

    if location_ok and _matches_swe(job):
        job.category = "SWE"
        return True
    if (location_ok or not EE_REQUIRE_LOCATION) and _matches_internship(job, EE_TITLE_RE):
        job.category = "EE"
        return True
    if (ie_location_ok or not IE_REQUIRE_LOCATION) and _matches_internship(job, IE_TITLE_RE):
        job.category = "IE"
        return True
    return False


# --------------------------------------------------------------------------- #
# URL / text helpers
# --------------------------------------------------------------------------- #
_TRACKING = re.compile(
    r"^(utm_.*|ref|referrer|source|src|s|gh_src|trk|trackingid|refid|fbclid|gclid)$", re.I
)


def normalize_url(url: str) -> str:
    parts = urlsplit(url.strip())
    query = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True)
             if not _TRACKING.match(k)]
    return urlunsplit((parts.scheme.lower(), parts.netloc.lower(),
                       parts.path.rstrip("/"), urlencode(query), ""))


_TAG_RE = re.compile(r"<[^>]+>")
_EMOJI_RE = re.compile("[\U0001F000-\U0001FAFF\u2600-\u27BF\uFE0F\u200d]+")
_MD_LINK_TEXT_RE = re.compile(r"\[([^\]]*)\]\([^)]*\)")


_SUMMARY_RE = re.compile(r"<summary>.*?</summary>", re.S | re.I)
_BREAK_RE = re.compile(r"</?(br|div|p|li|ul)\b[^>]*>", re.I)
_SEMI_RUN_RE = re.compile(r"(\s*;\s*)+")
_SPACE_RE = re.compile(r"\s+")


def clean_text(raw: str) -> str:
    raw = _SUMMARY_RE.sub("", raw)
    raw = _BREAK_RE.sub("; ", raw)
    raw = html.unescape(_TAG_RE.sub("", raw))
    raw = _MD_LINK_TEXT_RE.sub(r"\1", raw)
    raw = _EMOJI_RE.sub("", raw)
    raw = raw.replace("**", "").replace("__", "")
    raw = _SEMI_RUN_RE.sub("; ", raw)
    return _SPACE_RE.sub(" ", raw).strip(" ;")


def clean_pay(raw: str) -> str:
    """Keeps a pay cell only if it looks like pay (has a number, short)."""
    text = clean_text(raw)
    return text if re.search(r"\d", text) and len(text) <= 40 else ""


_HREF_RE = re.compile(r'href="([^"]+)"', re.I)
_MD_URL_RE = re.compile(r"\]\((https?://[^)\s]+)\)")


def extract_apply_url(cell: str) -> str:
    urls = [html.unescape(u) for u in _HREF_RE.findall(cell)] + _MD_URL_RE.findall(cell)
    urls = [u for u in urls if u.startswith("http")]
    # Simplify puts a direct link first and a simplify.jobs link second; prefer direct.
    direct = [u for u in urls if "simplify.jobs" not in u]
    return (direct or urls or [""])[0]


# --------------------------------------------------------------------------- #
# GitHub Markdown / HTML table scraping
# --------------------------------------------------------------------------- #
_HEADER_NAMES = {
    "company": {"company"},
    "role": {"role", "position", "title"},
    "location": {"location", "locations"},
    "apply": {"apply", "posting", "application", "link"},
    "salary": {"salary", "pay", "compensation"},          # optional: most lists have none
}
_REQUIRED_COLUMNS = ("company", "role", "location", "apply")
# A job can only ever match a category if its title matches one of these, so rows that
# don't are dropped before the costly cleanup / hashing.
_RELEVANT_TITLE_RE = re.compile(
    "|".join((SWE_TITLE_RE.pattern, EE_TITLE_RE.pattern, IE_TITLE_RE.pattern)), re.I
)
_TR_RE = re.compile(r"<tr[^>]*>(.*?)</tr>", re.S | re.I)
_CELL_RE = re.compile(r"<t[dh][^>]*>(.*?)</t[dh]>", re.S | re.I)
_SEPARATOR_RE = re.compile(r":?-{3,}:?")


def _pipe_rows(text: str):
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("|") and s.endswith("|"):
            yield [c.strip() for c in re.split(r"(?<!\\)\|", s)[1:-1]]


def _html_rows(text: str):
    for tr in _TR_RE.findall(text):
        cells = _CELL_RE.findall(tr)
        if cells:
            yield cells


def _column_map(cells: list[str]) -> dict[str, int] | None:
    found: dict[str, int] = {}
    for i, cell in enumerate(cells):
        name = clean_text(cell).lower()
        for key, options in _HEADER_NAMES.items():
            if name in options and key not in found:
                found[key] = i
    return found if all(k in found for k in _REQUIRED_COLUMNS) else None


def _extract_jobs(rows, source: str) -> list[Job]:
    jobs: list[Job] = []
    colmap: dict[str, int] | None = None
    last_company_raw = ""
    for cells in rows:
        if all(_SEPARATOR_RE.fullmatch(c.strip()) for c in cells):
            continue
        # Header rows are rare; don't run the expensive cleanup on every data row.
        # Header cells are short ("Company"); data cells hold long links that can contain
        # the word too (utm_medium=company), so the length check matters.
        if any(len(c) < 30 and "company" in c.lower() for c in cells):
            header = _column_map(cells)
            if header:
                colmap, last_company_raw = header, ""
                continue
        if not colmap or len(cells) <= max(colmap.values()):
            continue
        if "🔒" in "".join(cells):          # closed postings on Simplify
            continue
        raw_company = cells[colmap["company"]]
        if "↳" in raw_company or not raw_company.strip():
            raw_company = last_company_raw  # continuation row -> same company as above
        else:
            last_company_raw = raw_company
        title = clean_text(cells[colmap["role"]])
        if not _RELEVANT_TITLE_RE.search(title):
            continue
        company = clean_text(raw_company)
        location = clean_text(cells[colmap["location"]])
        url = extract_apply_url(cells[colmap["apply"]])
        salary = clean_pay(cells[colmap["salary"]]) if "salary" in colmap else ""
        if company and title and url:
            jobs.append(Job(company, title, location or "Not listed", url, source, salary=salary))
    return jobs


def parse_job_table(markdown: str, source: str) -> list[Job]:
    """Handles both pipe tables and raw HTML <tr> tables in one document."""
    return _extract_jobs(_pipe_rows(markdown), source) + _extract_jobs(_html_rows(markdown), source)


def _http_session() -> requests.Session:
    session = requests.Session()
    retry = Retry(total=3, backoff_factor=1.5, status_forcelist=(429, 500, 502, 503, 504),
                  allowed_methods=("GET",))
    session.mount("https://", HTTPAdapter(max_retries=retry))
    session.headers["User-Agent"] = "job-alert-discord-bot/1.0"
    return session


def fetch_repo_jobs(source: str, url: str) -> list[Job]:
    """Blocking; run in a worker thread. Never raises."""
    try:
        resp = _http_session().get(url, timeout=30)
        resp.raise_for_status()
        jobs = parse_job_table(resp.text, source)
        log.info("%s -> %d relevant rows", source, len(jobs))
        return jobs
    except Exception:
        log.exception("Failed to fetch %s", source)
        return []


# --------------------------------------------------------------------------- #
# LinkedIn + Indeed via JobSpy
# --------------------------------------------------------------------------- #
def _s(value) -> str:
    """Pandas-safe string conversion (None / NaN / NA -> '')."""
    if value is None:
        return ""
    try:
        if value != value:
            return ""
    except (TypeError, ValueError):
        return ""
    return str(value).strip()


def _preload_jobspy() -> None:
    try:
        import jobspy  # noqa: F401
    except ImportError:
        pass


_CURRENCY_SYMBOLS = {"USD": "$", "CAD": "CA$", "GBP": "£", "EUR": "€"}
_INTERVAL_SUFFIX = {"yearly": "/yr", "hourly": "/hr", "monthly": "/mo", "weekly": "/wk", "daily": "/day"}


def _num(value) -> float | None:
    try:
        n = float(value)
    except (TypeError, ValueError):
        return None
    return None if n != n or n <= 0 else n          # drops NaN / zero


def format_pay(rec: dict) -> str:
    """Builds text like '$25-$35/hr' or '$120k-$150k/yr' from JobSpy's pay columns."""
    lo, hi = _num(rec.get("min_amount")), _num(rec.get("max_amount"))
    if lo is None and hi is None:
        return ""
    interval = _s(rec.get("interval")).lower()
    code = (_s(rec.get("currency")) or "USD").upper()
    symbol = _CURRENCY_SYMBOLS.get(code, f"{code} ")

    def fmt(n: float) -> str:
        if interval == "yearly" and n >= 1000:
            return f"{symbol}{n / 1000:g}k"
        text = f"{n:,.2f}"
        return symbol + (text[:-3] if text.endswith(".00") else text)

    lo, hi = lo or hi, hi or lo
    amount = fmt(lo) if lo == hi else f"{fmt(lo)}–{fmt(hi)}"
    return amount + _INTERVAL_SUFFIX.get(interval, "")


_jobspy_lock = threading.Lock()
_jobspy_offset = 0          # where the next run starts in JOBSPY_SEARCHES (rotates)


def fetch_jobspy_jobs() -> list[Job]:
    """Blocking; run in a worker thread. Never raises."""
    global _jobspy_offset
    if not ENABLE_JOBSPY:
        return []
    try:
        from jobspy import scrape_jobs
    except ImportError:
        log.error("python-jobspy is not installed; skipping LinkedIn/Indeed")
        return []
    if not _jobspy_lock.acquire(blocking=False):
        log.warning("A previous JobSpy run is still going; skipping JobSpy this cycle")
        return []

    try:
        jobs: list[Job] = []
        total = len(JOBSPY_SEARCHES)
        start = _jobspy_offset % total
        order = JOBSPY_SEARCHES[start:] + JOBSPY_SEARCHES[:start]
        deadline = time.monotonic() + JOBSPY_TIME_BUDGET
        attempted = 0

        for term, location in order:
            if attempted >= JOBSPY_MAX_SEARCHES:
                log.info("JobSpy search cap reached (%d/%d); the rest go first next cycle",
                         attempted, total)
                break
            if time.monotonic() > deadline:
                log.warning("JobSpy time budget hit after %d/%d searches; the rest go first next cycle",
                            attempted, total)
                break
            attempted += 1
            log.info("JobSpy search %d/%d: %r in %r", attempted, total, term, location)
            try:
                df = scrape_jobs(
                    site_name=JOBSPY_SITES,
                    search_term=term,
                    location=location,
                    results_wanted=JOBSPY_RESULTS,
                    hours_old=JOBSPY_HOURS_OLD,
                    country_indeed="USA",
                    linkedin_fetch_description=False,   # True is slower and gets blocked sooner
                    proxies=PROXIES or None,
                    verbose=0,
                )
            except Exception as exc:
                # Timeouts / blocks are expected from LinkedIn; keep the log to one line.
                log.warning("JobSpy search failed (%s: %s): %r in %r",
                            type(exc).__name__, str(exc)[:120], term, location,
                            exc_info=log.isEnabledFor(logging.DEBUG))
                continue

            for rec in df.to_dict("records"):
                url = _s(rec.get("job_url"))
                title, company = _s(rec.get("title")), _s(rec.get("company"))
                if not (url and title and company):
                    continue
                loc = _s(rec.get("location")) or "Not listed"
                if rec.get("is_remote") is True:
                    loc += " (Remote)"
                site = _s(rec.get("site")).lower()
                jobs.append(Job(
                    company=company, title=title, location=loc, url=url,
                    source={"linkedin": "LinkedIn", "indeed": "Indeed"}.get(site, site.title() or "JobSpy"),
                    description=_s(rec.get("description"))[:3000],
                    salary=format_pay(rec),
                    from_jobspy=True,
                    search_term=term,
                ))
            time.sleep(random.uniform(JOBSPY_DELAY, JOBSPY_DELAY * 1.5))   # spreads load; sleeping costs no CPU

        _jobspy_offset = start + attempted
        log.info("JobSpy -> %d rows from %d/%d searches", len(jobs), attempted, total)
        return jobs
    finally:
        _jobspy_lock.release()


# --------------------------------------------------------------------------- #
# SQLite store
# --------------------------------------------------------------------------- #
class JobStore:
    def __init__(self, path: str) -> None:
        self.conn = sqlite3.connect(path)
        self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS seen_jobs (
                url_key     TEXT PRIMARY KEY,
                fingerprint TEXT NOT NULL,
                company     TEXT,
                title       TEXT,
                source      TEXT,
                first_seen  TEXT DEFAULT CURRENT_TIMESTAMP
            );
            CREATE INDEX IF NOT EXISTS idx_seen_fingerprint ON seen_jobs (fingerprint);
            CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);
            """
        )
        self.conn.commit()

    def is_first_run(self) -> bool:
        row = self.conn.execute("SELECT 1 FROM meta WHERE key = 'seeded'").fetchone()
        return row is None

    def finish_first_run(self) -> None:
        self.conn.execute("INSERT OR REPLACE INTO meta VALUES ('seeded', '1')")
        self.conn.commit()

    def is_new(self, job: Job) -> bool:
        row = self.conn.execute(
            "SELECT 1 FROM seen_jobs WHERE url_key = ? OR fingerprint = ? LIMIT 1",
            (job.url_key, job.fingerprint),
        ).fetchone()
        return row is None

    def mark_seen(self, jobs: list[Job]) -> None:
        self.conn.executemany(
            "INSERT OR IGNORE INTO seen_jobs (url_key, fingerprint, company, title, source) "
            "VALUES (?, ?, ?, ?, ?)",
            [(j.url_key, j.fingerprint, j.company, j.title, j.source) for j in jobs],
        )
        self.conn.commit()

    def close(self) -> None:
        self.conn.close()


# --------------------------------------------------------------------------- #
# Discord
# --------------------------------------------------------------------------- #
SOURCE_COLORS = {"LinkedIn": 0x0A66C2, "Indeed": 0x2557A7, "GitHub": 0x2DA44E}


def _trunc(text: str, limit: int) -> str:
    return text if len(text) <= limit else text[: limit - 1] + "…"


def build_embed(job: Job) -> discord.Embed:
    color = next((c for prefix, c in SOURCE_COLORS.items() if job.source.startswith(prefix)), 0x5865F2)
    safe_url = job.url.replace(")", "%29")
    embed = discord.Embed(
        title=_trunc(f"{job.company} — {job.title}", 256),
        url=job.url,
        description=f"[**Apply here →**]({safe_url})",
        color=color,
        timestamp=discord.utils.utcnow(),
    )
    embed.add_field(name="Company", value=_trunc(job.company, 1024), inline=True)
    embed.add_field(name="Job Title", value=_trunc(job.title, 1024), inline=True)
    embed.add_field(name="Location", value=_trunc(job.location, 300), inline=False)  # some lists have 30+ cities
    embed.add_field(name="Pay", value=_trunc(job.salary or "Not listed", 1024), inline=False)
    embed.add_field(name="Source", value=_trunc(job.source, 1024), inline=False)
    if job.category == "SWE" and job.stack_match:
        embed.set_author(name="⭐ React / TypeScript / JavaScript / Frontend match")
    elif job.category == "EE":
        embed.set_author(name="🔌 Electrical / Hardware / Embedded internship")
    elif job.category == "IE":
        embed.set_author(name="🏭 Industrial / Process / Supply Chain internship")
    embed.set_footer(text=f"New {job.category} posting")
    return embed


MAX_EMBEDS_PER_MESSAGE = 10      # Discord's hard limit
MAX_EMBED_CHARS = 5500           # Discord caps total embed text at 6000 per message


def _chunk_jobs(jobs: list[Job]):
    """Yields lists of (job, embed) that each fit in a single Discord message."""
    chunk: list[tuple[Job, discord.Embed]] = []
    size = 0
    for job in jobs:
        embed = build_embed(job)
        if chunk and (len(chunk) >= MAX_EMBEDS_PER_MESSAGE or size + len(embed) > MAX_EMBED_CHARS):
            yield chunk
            chunk, size = [], 0
        chunk.append((job, embed))
        size += len(embed)
    if chunk:
        yield chunk


class JobBot(discord.Client):
    def __init__(self, channel_id: int) -> None:
        super().__init__(intents=discord.Intents.default())
        self.channel_id = channel_id
        self.store = JobStore(DB_PATH)

    async def setup_hook(self) -> None:
        log.info("Low-power mode: %s | JobSpy: up to %d searches/run, %d results each, %.0fs pauses",
                 LOW_POWER, JOBSPY_MAX_SEARCHES, JOBSPY_RESULTS, JOBSPY_DELAY)
        self.job_check.start()

    async def close(self) -> None:
        self.store.close()
        await super().close()

    async def _channel(self):
        channel = self.get_channel(self.channel_id)
        if channel is None:
            try:
                channel = await self.fetch_channel(self.channel_id)
            except discord.HTTPException:
                log.error("Can't access channel %s. Check CHANNEL_ID and bot permissions.", self.channel_id)
        return channel

    @tasks.loop(hours=1)
    async def job_check(self) -> None:
        started = time.monotonic()
        log.info("Cycle started")
        try:
            await self._run_cycle()
        except Exception:
            # Swallow so one bad run doesn't kill the hourly loop.
            log.exception("Job check cycle failed")
        log.info("Cycle finished in %.0fs", time.monotonic() - started)

    async def _jobspy_bounded(self) -> list[Job]:
        """JobSpy with a hard stop, so a hung scrape can't block posting forever."""
        try:
            return await asyncio.wait_for(
                asyncio.to_thread(fetch_jobspy_jobs), timeout=JOBSPY_TIME_BUDGET + 300
            )
        except asyncio.TimeoutError:
            log.error("JobSpy exceeded its hard timeout; continuing without it this cycle")
            return []

    @job_check.before_loop
    async def _before_job_check(self) -> None:
        await self.wait_until_ready()
        if ENABLE_JOBSPY:
            await asyncio.to_thread(_preload_jobspy)   # the import alone is ~0.6s of CPU
        await asyncio.sleep(STARTUP_DELAY)

    async def _run_cycle(self) -> None:
        channel = await self._channel()
        if channel is None:
            return

        # Blocking network work goes to threads so the Discord heartbeat stays alive.
        jobspy_task = asyncio.create_task(self._jobspy_bounded())
        batches = []
        for name, url in REPO_SOURCES.items():     # one at a time, so CPU never spikes
            batches.append(await asyncio.to_thread(fetch_repo_jobs, name, url))
            await asyncio.sleep(GITHUB_PAUSE)
        batches.append(await jobspy_task)

        matched: list[Job] = []
        kept: dict[str, Job] = {}                  # url_key / fingerprint -> job already kept
        for job in (j for batch in batches for j in batch):
            if not passes_filters(job):
                continue
            twin = kept.get(job.url_key) or kept.get(job.fingerprint)
            if twin:
                if job.salary and not twin.salary:  # duplicate from another source has the pay
                    twin.salary = job.salary
                continue
            kept[job.url_key] = kept[job.fingerprint] = job
            matched.append(job)

        new_jobs = [j for j in matched if self.store.is_new(j)]

        def by_cat(jobs: list[Job]) -> str:
            counts = Counter(j.category for j in jobs)
            return " ".join(f"{c}={counts[c]}" for c in CATEGORY_PING_IDS)

        jobspy_jobs = batches[-1]
        log.info("Matched: %s | New: %s | JobSpy: %d rows fetched, %d matched (%s)",
                 by_cat(matched), by_cat(new_jobs), len(jobspy_jobs),
                 sum(1 for j in matched if j.from_jobspy),
                 by_cat([j for j in matched if j.from_jobspy]))

        # First ever run: record what's already out there instead of flooding the channel.
        if self.store.is_first_run():
            self.store.finish_first_run()
            if SEED_ON_FIRST_RUN:
                self.store.mark_seen(new_jobs)
                await channel.send(
                    f"✅ Job bot is live. Indexed **{len(new_jobs)}** current matching postings. "
                    "You'll only get pinged for new ones from now on."
                )
                return

        new_jobs.sort(key=lambda j: not j.stack_match)   # stack matches first
        for category in CATEGORY_PING_IDS:
            group = [j for j in new_jobs if j.category == category]
            if not group:
                continue                                  # nothing new -> no ping
            await self._send_group(channel, category, group[:MAX_PER_CYCLE])
            if len(group) > MAX_PER_CYCLE:
                log.info("%d more new %s jobs deferred to the next cycle",
                         len(group) - MAX_PER_CYCLE, category)

    async def _send_group(self, channel, category: str, jobs: list[Job]) -> None:
        """One ping for the whole category, then all its embeds (10 per message max)."""
        plural = "" if len(jobs) == 1 else "s"
        ping = f"<@{CATEGORY_PING_IDS[category]}> **{len(jobs)} new {category} posting{plural}**"
        ping_sent = False
        for chunk in _chunk_jobs(jobs):
            try:
                # Mentions inside embeds don't notify anyone, so the ping goes in `content`.
                await channel.send(content=None if ping_sent else ping,
                                   embeds=[embed for _, embed in chunk])
            except discord.HTTPException:
                log.exception("Failed to send %d %s job(s)", len(chunk), category)
                continue                                  # not marked seen -> retried next hour
            ping_sent = True
            self.store.mark_seen([job for job, _ in chunk])
            await asyncio.sleep(1.5)                      # stay well under Discord rate limits

    async def on_ready(self) -> None:
        log.info("Logged in as %s", self.user)


def main() -> None:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    token, channel = os.getenv("DISCORD_TOKEN"), os.getenv("CHANNEL_ID")
    if not token or not channel or not channel.isdigit():
        sys.exit("Set DISCORD_TOKEN and a numeric CHANNEL_ID (see .env.example).")
    JobBot(int(channel)).run(token, log_handler=None)


if __name__ == "__main__":
    main()