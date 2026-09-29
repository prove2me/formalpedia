-- Prove2me | Theorems.Thm_Freiman_gap_minimum_left_initial
-- name    : Freiman.gap_minimum_left_initial
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:24.062768+00:00
-- url     : https://prove2.me/theorems/c107eefb-e8df-4b92-b01d-d887c0a11c34
-- title:
--   gap minimum left initial
-- statement:
--   The fixed seed and the finite initial greedy rows give every allowed left digit comparison before the repeating suffix state.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; greedy left table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_left_initial (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) (n : ℕ) (hn : n < 4) (hp : gapSameBefore (gapLeftTail a) gapBLeft n) : gapLowerDigit (gapLeftTail a) gapBLeft n := by
  sorry

end Freiman
