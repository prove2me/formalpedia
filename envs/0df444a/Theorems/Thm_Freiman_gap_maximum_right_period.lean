-- Prove2me | Theorems.Thm_Freiman_gap_maximum_right_period
-- name    : Freiman.gap_maximum_right_period
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:36.445163+00:00
-- url     : https://prove2.me/theorems/a4b59cd1-9146-4754-ae63-1aa24c705436
-- title:
--   gap maximum right period
-- statement:
--   Each of the six displayed suffix states excludes every improving digit, for every repeated period; the suffix and parity return after six positions.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; six-state periodic greedy table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_right_period (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) (k r : ℕ) (hr : r < 6) (hp : gapSameBefore (gapRightTail a) gapARight (7+6*k+r)) : gapUpperDigit (gapRightTail a) gapARight (7+6*k+r) := by
  sorry

end Freiman
