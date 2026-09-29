-- Prove2me | Theorems.Thm_Freiman_upper_choice_path
-- name    : Freiman.upper_choice_path
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:11.45296+00:00
-- url     : https://prove2.me/theorems/596eae54-6a35-4b8e-a3f1-eb13b549dd01
-- title:
--   Choose an infinite target-preserving path
-- statement:
--   Assuming the one-deletion covering property, two normal binary trees admit an infinite path preserving any target from the initial derived intervals and splitting a currently longer side at every step.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Proof of m2a:normal-sum, first paragraph.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_choice_path (step : ∀ C D L R : upperInterval, 0 < upperLength C → upperLength C ≤ upperLength D → upperNormalSplit D L R → upperDerived C D ⊆ upperDerived C L ∪ upperDerived C R) (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S) (z : ℝ) (hz : z ∈ upperDerived (T []) (S [])) :
    ∃ u v : ℕ → List Bool, upperPath T S u v z := by
  sorry

end Freiman
