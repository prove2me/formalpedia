-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_unrestricted_occupation_set_identity
-- name    : Kyprianou.Ch08.StageB.p2m89_unrestricted_occupation_set_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:58:14.661802+00:00
-- url     : https://prove2.me/theorems/ac87340c-1ef1-4c40-a648-ffcee2754928
-- title:
--   8.9: unrestricted occupation identity on measurable sets
-- statement:
--   Core full-line resolvent density identity on measurable sets. Derive via a translated half-line potential and the q-positive scale asymptotics.
-- source:
--   Kyprianou (2006), Chapter 8, source results 8.7–8.9.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- 8.9: unrestricted occupation identity on measurable sets. -/
theorem p2m89_unrestricted_occupation_set_identity :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), 0 < q →
      ∀ (A : Set ℝ), MeasurableSet A →
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal
        (unrestrictedPotentialDensity ψ q (W q) (x - y)))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  sorry

end Kyprianou.Ch08.StageB
