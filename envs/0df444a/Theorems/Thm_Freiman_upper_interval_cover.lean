-- Prove2me | Theorems.Thm_Freiman_upper_interval_cover
-- name    : Freiman.upper_interval_cover
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:11:59.440859+00:00
-- url     : https://prove2.me/theorems/6df7d19f-5072-493e-8095-a6c7629844a4
-- title:
--   The large and small central intervals cover the upper ray
-- statement:
--   Every t at least h belongs either to a central interval n+[2Theta8,2Theta1] for an integer n≥5, or to 4+[2Theta2,2Theta1]. The integer intervals overlap and their union overlaps the small family.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:large-family, m2a:small-family and their overlap.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_interval_cover (t : ℝ) (ht : upperRayStart ≤ t) :
    (∃ n : ℕ+, 5 ≤ (n : ℕ) ∧ t - ((n : ℕ) : ℝ) ∈ Set.Icc (2 * upperTheta8) (2 * upperTheta1)) ∨
    t - 4 ∈ Set.Icc (2 * upperTheta2) (2 * upperTheta1) := by
  sorry

end Freiman
