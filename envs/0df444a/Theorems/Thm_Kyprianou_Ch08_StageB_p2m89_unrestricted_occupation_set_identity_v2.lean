-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_unrestricted_occupation_set_identity_v2
-- name    : Kyprianou.Ch08.StageB.p2m89_unrestricted_occupation_set_identity_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:15:36.752388+00:00
-- url     : https://prove2.me/theorems/33cf8321-6b73-409d-84cc-a8da6fcb2949
-- title:
--   8.9: corrected unrestricted occupation identity on measurable sets
-- statement:
--   Unrestricted resolvent on measurable sets, with density evaluated at destination minus starting level.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.9. Correct the sign of the displacement to y - x; the existing density definition is retained. Supersedes ac87340c-1ef1-4c40-a648-ffcee2754928.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- 8.9: unrestricted occupation identity on measurable sets. -/
theorem p2m89_unrestricted_occupation_set_identity_v2 :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), 0 < q →
      ∀ (A : Set ℝ), MeasurableSet A →
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal
        (unrestrictedPotentialDensity ψ q (W q) (y - x)))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  sorry

end Kyprianou.Ch08.StageB
