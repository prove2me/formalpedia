-- Prove2me | Theorems.Thm_Freiman_upper_small_noncentral
-- name    : Freiman.upper_small_noncentral
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:08.165722+00:00
-- url     : https://prove2.me/theorems/b4b0b462-9c26-4acb-8577-af8e607dd0e5
-- title:
--   Uniform noncentral bound for the small-family padded models
-- statement:
--   At a noncentral 4 combine the inward periodic bound with the outward A bound. All other digits have local value below 5<B. Thus B bounds every noncentral position of every padded truncation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:small-bound and m2a:completed-bounds.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_small_noncentral (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3) (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) (j : ℕ) (i : ℤ) (hi : i ≠ 0) :
    localValue (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i ≤ upperSmallBound := by
  sorry

end Freiman
