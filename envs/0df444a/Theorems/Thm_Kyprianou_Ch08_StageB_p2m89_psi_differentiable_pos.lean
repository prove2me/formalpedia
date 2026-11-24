-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_psi_differentiable_pos
-- name    : Kyprianou.Ch08.StageB.p2m89_psi_differentiable_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:32:54.047424+00:00
-- url     : https://prove2.me/theorems/7fbf69ff-af5e-485c-8d62-23d45cbe4069
-- title:
--   Differentiability of the source Laplace exponent at every positive argument.
-- statement:
--   Differentiability of the source Laplace exponent at every positive argument.
-- source:
--   Kyprianou (2006), Theorem 8.9: differentiability of the positive right root.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Differentiability of the source Laplace exponent at every positive argument. -/
theorem p2m89_psi_differentiable_pos :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      ∀ β : ℝ, 0 < β → DifferentiableAt ℝ ψ β := by
  sorry

end Kyprianou.Ch08.StageB
