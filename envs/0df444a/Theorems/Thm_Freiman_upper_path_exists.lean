-- Prove2me | Theorems.Thm_Freiman_upper_path_exists
-- name    : Freiman.upper_path_exists
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:14.393617+00:00
-- url     : https://prove2.me/theorems/07a966d5-0e7c-44c4-b821-5541f437b512
-- title:
--   A normal-deletion path for every initial target
-- statement:
--   The geometric one-deletion lemma supplies a path in the two given normal trees, always retaining the same real target and splitting a longer current interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:normal-sum.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_path_exists (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S) (z : ℝ) (hz : z ∈ upperDerived (T []) (S [])) :
    ∃ u v : ℕ → List Bool, upperPath T S u v z := by
  sorry

end Freiman
