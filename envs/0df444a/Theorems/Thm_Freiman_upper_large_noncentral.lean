-- Prove2me | Theorems.Thm_Freiman_upper_large_noncentral
-- name    : Freiman.upper_large_noncentral
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:02.556272+00:00
-- url     : https://prove2.me/theorems/60f9dcc0-383c-4c3d-8023-04818f78aa5d
-- title:
--   Uniform noncentral bound in every large-family truncation
-- statement:
--   Padding either admissible outward tail by 3 preserves the local estimate at all noncentral positions: digits≤3 give a value below 5, and a digit 4 has its inward neighbor at least 3, giving the bound 16/3.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:large-bound and m2a:completed-bounds.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_large_noncentral (n : ℕ+) (hn : 5 ≤ (n : ℕ)) (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hr : upperAdmissible r) (j : ℕ) (i : ℤ) (hi : i ≠ 0) :
    localValue (upperPad (upperCentral n l r) j) i ≤ (16 / 3 : ℝ) := by
  sorry

end Freiman
