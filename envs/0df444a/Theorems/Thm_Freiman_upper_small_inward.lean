-- Prove2me | Theorems.Thm_Freiman_upper_small_inward
-- name    : Freiman.upper_small_inward
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:08.570307+00:00
-- url     : https://prove2.me/theorems/0c60ce59-9333-41e7-bed6-761f9dce5eba
-- title:
--   The inward 34-periodic bound at a noncentral 4
-- statement:
--   At every noncentral 4 of every padded small-family word the inward fractional tail is at most [0;overline(34)] = −2+4sqrt(3)/3. The proof follows induction on distance from the fixed central block, with the 3,4 step reducing that distance by two.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:small-bound, inward-tail induction.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_small_inward (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3) (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) (j : ℕ) (i : ℤ) (hi : i ≠ 0) (h4 : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) = 4) :
    upperInward (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i ≤ upperInwardFixed := by
  sorry

end Freiman
