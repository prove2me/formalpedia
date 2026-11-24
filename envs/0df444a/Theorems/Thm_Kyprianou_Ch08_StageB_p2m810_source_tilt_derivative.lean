-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_source_tilt_derivative
-- name    : Kyprianou.Ch08.StageB.p2m810_source_tilt_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:12:31.607857+00:00
-- url     : https://prove2.me/theorems/60e60325-b96a-4aff-9e74-3c39e2abafcd
-- title:
--   Source tilted right derivative
-- statement:
--   Apply the proved right derivative of Theorem 8.2 and the tilted derivative product rule.
-- source:
--   Kyprianou (2006), Theorem 8.10.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Source tilted right derivative -/
theorem p2m810_source_tilt_derivative :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a θ : ℝ), 0 ≤ q → 0 < a →
      HasDerivWithinAt (tiltedScale θ (W q))
        (derivWithin (tiltedScale θ (W q)) (Ici a) a) (Ici a) a ∧
      derivWithin (tiltedScale θ (W q)) (Ici a) a + θ * tiltedScale θ (W q) a =
        Real.exp (-θ*a) * derivWithin (W q) (Ici a) a := by
  sorry
end Kyprianou.Ch08.StageB
