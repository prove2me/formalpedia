-- Prove2me | Theorems.Thm_Freiman_upper_small_low_digits
-- name    : Freiman.upper_small_low_digits
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:15.647832+00:00
-- url     : https://prove2.me/theorems/453d0cd2-1dbb-43a8-b7d1-2c03b8d5dc90
-- title:
--   Small-family positions whose digit is not 4 have height below 5
-- statement:
--   Every noncentral digit other than 4 is at most 3; both fractional tails are strictly below 1, including for every truncation padded by 3.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. The paragraph after m2a:small-bound.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_small_low_digits (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3) (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) (j : ℕ) (i : ℤ) (hi : i ≠ 0) (h4 : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) ≠ 4) :
    localValue (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i < 5 := by
  sorry

end Freiman
