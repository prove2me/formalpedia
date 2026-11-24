-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_exit_ratio
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_exit_ratio
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:12:37.567377+00:00
-- url     : https://prove2.me/theorems/e7b0bb9e-68f1-49c9-aed6-368def178254
-- title:
--   Actual infimum-reflected exit ratio
-- statement:
--   Combine the reset sandwich with quotient convergence and the elementary squeezing lemma.
-- source:
--   Kyprianou (2006), Theorem 8.10.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Actual infimum-reflected exit ratio -/
theorem p2m810_inf_exit_ratio :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      (∫ ω, discountedAt q (reflectedInfExit D.X x a ω) ∂P) =
        Zscale q (W q) x / Zscale q (W q) a := by
  sorry
end Kyprianou.Ch08.StageB
