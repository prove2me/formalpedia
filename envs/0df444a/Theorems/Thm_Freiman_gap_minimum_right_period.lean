-- Prove2me | Theorems.Thm_Freiman_gap_minimum_right_period
-- name    : Freiman.gap_minimum_right_period
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:34.943781+00:00
-- url     : https://prove2.me/theorems/08e1cb71-5bd5-4395-89ed-66b9ed6b1431
-- title:
--   gap minimum right period
-- statement:
--   Each of the six displayed suffix states excludes every improving digit, for every repeated period; the exceptional first right period is retained.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; six-state periodic greedy table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_right_period (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) (k r : ℕ) (hr : r < 6) (hp : gapSameBefore (gapRightTail a) gapBRight (4+6*k+r)) : gapLowerDigit (gapRightTail a) gapBRight (4+6*k+r) := by
  sorry

end Freiman
