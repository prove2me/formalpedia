-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_cycle_factor
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_cycle_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:26:10.092344+00:00
-- url     : https://prove2.me/theorems/cb2645cf-1891-4796-847f-6db6e86be951
-- title:
--   Two-sided exit renewal factors yield reset quotient
-- statement:
--   Apply the proved arbitrary-family upper and lower exit formulas. The first upper factor from zero is positive and the disjoint discounted exit payoffs have total mass at most one. The algebraic renewal quotient then gives the stated equality.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii), and Theorem 8.1.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Two-sided exit renewal factors yield reset quotient -/
theorem p2m810_inf_cycle_factor :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ ε b : ℝ, 0 < ε → 0 < b → x ≤ b →
      let A := fun y : ℝ => upBeforeDownExpectation P D.X q (y+ε) (b+ε)
      let B := fun y : ℝ => downBeforeUpExpectation P D.X q (y+ε) (b+ε)
      0 < A 0 ∧ B 0 < 1 ∧ 0 ≤ B x ∧
      A x + B x * (A 0 / (1-B 0)) =
        (Zscale q (W q) (x+ε) - W q (x+ε) *
          ((Zscale q (W q) ε - 1) / W q ε)) /
        (Zscale q (W q) (b+ε) - W q (b+ε) *
          ((Zscale q (W q) ε - 1) / W q ε)) := by
  sorry
end Kyprianou.Ch08.StageB
