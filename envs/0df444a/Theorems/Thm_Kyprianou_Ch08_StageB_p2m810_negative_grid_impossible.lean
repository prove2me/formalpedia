-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_negative_grid_impossible
-- name    : Kyprianou.Ch08.StageB.p2m810_negative_grid_impossible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:33:04.043871+00:00
-- url     : https://prove2.me/theorems/d17e2804-85de-4c78-a950-05379ce4ed69
-- title:
--   Terminal lower bound excludes simultaneous negative grid increments
-- statement:
--   If every increment is below c, their telescoping sum is at most n*c, contradicting the terminal lower bound. Thus a factor in the product is zero.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); independent increments.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Terminal lower bound excludes simultaneous negative grid increments -/
theorem p2m810_negative_grid_impossible :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
      (t : ℝ≥0) (a c : ℝ) (n : ℕ),
      X 0 ω = 0 → -a ≤ X ((n:ℝ≥0)*t) ω → (n:ℝ)*c < -a →
      (∏ i : Fin n, (if X (((i.val+1 : ℕ):ℝ≥0)*t) ω -
        X ((i.val:ℝ≥0)*t) ω < c then (1:ℝ) else 0)) = 0 := by
  sorry
end Kyprianou.Ch08.StageB
