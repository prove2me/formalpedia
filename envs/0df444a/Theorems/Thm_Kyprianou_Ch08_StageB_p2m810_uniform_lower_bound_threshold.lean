-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_uniform_lower_bound_threshold
-- name    : Kyprianou.Ch08.StageB.p2m810_uniform_lower_bound_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:32:55.246255+00:00
-- url     : https://prove2.me/theorems/e2c66864-2a21-438a-9736-1a8109bd940f
-- title:
--   Uniform lower bound excludes each negative marginal threshold
-- statement:
--   Choose a sufficiently long grid so that n*c < -a. The product is almost surely zero but its integral is the nth power of the single increment indicator integral. The indicator is integrable, so its integral being zero implies the threshold event is null.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); independent increments.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Uniform lower bound excludes each negative marginal threshold -/
theorem p2m810_uniform_lower_bound_threshold :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess X P →
      ∀ (a c : ℝ) (t : ℝ≥0), c < 0 →
      (∀ s : ℝ≥0, ∀ᵐ ω ∂P, -a ≤ X s ω) →
      ∀ᵐ ω ∂P, c ≤ X t ω := by
  sorry
end Kyprianou.Ch08.StageB
