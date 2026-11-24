-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_levy_negative_grid_product
-- name    : Kyprianou.Ch08.StageB.p2m810_levy_negative_grid_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:32:48.269803+00:00
-- url     : https://prove2.me/theorems/e267de81-65f6-4385-93f3-94e7188f4d02
-- title:
--   Equal-duration negative increment indicator product factors
-- statement:
--   Use finite-grid independent increments and stationary increment laws. Integrate the product of indicators of the same negative threshold.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); independent increments.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Equal-duration negative increment indicator product factors -/
theorem p2m810_levy_negative_grid_product :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess X P →
      ∀ (t : ℝ≥0) (c : ℝ) (n : ℕ),
      (∫ ω, ∏ i : Fin n, (if X (((i.val+1 : ℕ):ℝ≥0)*t) ω -
          X ((i.val:ℝ≥0)*t) ω < c then (1:ℝ) else 0) ∂P) =
        (∫ ω, if X t ω < c then (1:ℝ) else 0 ∂P)^n := by
  sorry
end Kyprianou.Ch08.StageB
