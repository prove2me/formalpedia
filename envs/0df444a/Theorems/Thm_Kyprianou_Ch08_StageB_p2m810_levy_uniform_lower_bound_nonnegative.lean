-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_levy_uniform_lower_bound_nonnegative
-- name    : Kyprianou.Ch08.StageB.p2m810_levy_uniform_lower_bound_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:30:07.094066+00:00
-- url     : https://prove2.me/theorems/381e0597-0865-4539-9510-b10624990e5b
-- title:
--   Uniform lower bound of Levy marginals forces nonnegative marginals
-- statement:
--   If some fixed-time marginal has positive probability of lying below a negative threshold, take sufficiently many independent equal-duration increments all below that threshold. Their sum violates the uniform lower bound with positive probability. Hence all marginals are nonnegative.
-- source:
--   Kyprianou (2006), Theorem 8.10(i), zero right slope.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Uniform lower bound of Levy marginals forces nonnegative marginals -/
theorem p2m810_levy_uniform_lower_bound_nonnegative :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess X P →
      ∀ a : ℝ, (∀ t : ℝ≥0, ∀ᵐ ω ∂P, -a ≤ X t ω) →
      ∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω := by
  sorry
end Kyprianou.Ch08.StageB
