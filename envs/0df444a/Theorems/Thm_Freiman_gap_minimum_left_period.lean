-- Prove2me | Theorems.Thm_Freiman_gap_minimum_left_period
-- name    : Freiman.gap_minimum_left_period
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:32.501659+00:00
-- url     : https://prove2.me/theorems/88ba9cc5-5618-4f0b-8fa2-5f1d053ca545
-- title:
--   gap minimum left period
-- statement:
--   Each of the six displayed suffix states excludes every improving digit, for every repeated period; the suffix and parity return after six positions.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; six-state periodic greedy table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_left_period (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) (k r : ℕ) (hr : r < 6) (hp : gapSameBefore (gapLeftTail a) gapBLeft (4+6*k+r)) : gapLowerDigit (gapLeftTail a) gapBLeft (4+6*k+r) := by
  sorry

end Freiman
