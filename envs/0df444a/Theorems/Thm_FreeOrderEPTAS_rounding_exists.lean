-- Prove2me | Theorems.Thm_FreeOrderEPTAS_rounding_exists
-- name    : FreeOrderEPTAS.rounding_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:56.713096+00:00
-- url     : https://prove2.me/theorems/23187f77-c458-4877-a9a5-949ead775a2c
-- title:
--   [GKPS06] as used on pp.11–12 — a rounding with (P1)–(P3) exists
-- statement:
--   For every (LP) and every vector $y$ meeting (S1)–(S3) there is a law of a binary vector $Y$ with properties (P1)–(P3).
--
--   This is the main result of Gandhi, Khuller, Parthasarathy and Srinivasan as translated on p.12. It shows that the rounding hypothesis of the mission's theorems can be met.
--
--   Differences from the source:
--   - reading: "their work provides a randomized construction" → a law with (P1)–(P3) exists; reason: the running time of the construction is not asserted on the page and is counted in this mission as one call
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, p.12, "Translating the main result of Gandhi et al. [GKPS06]"; [GKPS06], J. ACM 53(3), 2006

import Mathlib
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding

namespace FreeOrderEPTAS

/-- The result of Gandhi, Khuller, Parthasarathy and Srinivasan [GKPS06] as used on pp.11–12
(arXiv:2007.13121v3): for every vector `y` meeting (S1)–(S3), there is a law of `Y` with
(P1)–(P3). So `IsDependentRounding` is satisfiable. -/
theorem rounding_exists (P : LPData) (y : P.Vars) (hy : P.MeetsS123 y) :
    ∃ p : PMF (Assignment P.m P.n), RoundingProps P y p := by sorry

end FreeOrderEPTAS
