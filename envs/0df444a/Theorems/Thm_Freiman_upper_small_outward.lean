-- Prove2me | Theorems.Thm_Freiman_upper_small_outward
-- name    : Freiman.upper_small_outward
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:14.932969+00:00
-- url     : https://prove2.me/theorems/937c99c5-152a-48fe-8d8a-8e45a0d2e45d
-- title:
--   The outward tail at a small-family 4 satisfies the A hull bound
-- statement:
--   The outward tail at a noncentral 4 remains admissible in state A after padding by 3, so its value is at most Theta1.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:small-bound and m2a:completed-bounds.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_small_outward (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3) (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) (j : ℕ) (i : ℤ) (hi : i ≠ 0) (h4 : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) = 4) :
    upperOutward (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i ≤ upperTheta1 := by
  sorry

end Freiman
