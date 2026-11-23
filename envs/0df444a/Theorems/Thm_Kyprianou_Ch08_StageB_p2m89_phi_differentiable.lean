-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_differentiable
-- name    : Kyprianou.Ch08.StageB.p2m89_phi_differentiable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:58:04.882878+00:00
-- url     : https://prove2.me/theorems/4b8689ff-ccb8-4407-8800-39b117156f5d
-- title:
--   8.9: positive-discount right-root differentiability
-- statement:
--   Differentiability of the nonnegative right inverse Phi at positive discount; keep the source model, exponent and scale-family hypotheses.
-- source:
--   Kyprianou (2006), Chapter 8, source results 8.7–8.9.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- 8.9: positive-discount right-root differentiability. -/
theorem p2m89_phi_differentiable :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ q : ℝ, 0 < q → DifferentiableAt ℝ (Phi ψ) q := by
  sorry

end Kyprianou.Ch08.StageB
