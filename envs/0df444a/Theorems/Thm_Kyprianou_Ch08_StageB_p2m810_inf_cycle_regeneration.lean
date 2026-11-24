-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_cycle_regeneration
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_cycle_regeneration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:16:00.934233+00:00
-- url     : https://prove2.me/theorems/5878ce18-3aa5-48f4-8d02-516de4ccd7fc
-- title:
--   Infimum-reflection first-cycle strong Markov factorisation
-- statement:
--   The first upper exit contributes its own discount. On the event of a strict lower exit before the upper exit, the strong Markov property of the centred post-exit increments factors the discounted fresh infimum-reflected reward. Infinite equal clocks contribute zero. This obligation uses no comparison of the actual reflected exit with the cycle.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii), and Theorem 8.1.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Infimum-reflection first-cycle strong Markov factorisation -/
theorem p2m810_inf_cycle_regeneration :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ ε b : ℝ, 0 < ε → 0 < b → x ≤ b →
      let C := fun (b : ℝ) (ω : Ω) =>
        let u := tauPlus (shifted D.X (x+ε)) (b+ε) ω
        let v := tauMinus (shifted D.X (x+ε)) 0 ω
        let r : ℝ≥0 := match v with
          | ⊤ => 0
          | (s : ℝ≥0) => s
        if u < v then discountedAt q u else
          if v < u then discountedAt q v *
            discountedAt q (reflectedInfExit
              (fun t w => D.X (r+t) w - D.X r w) 0 a ω)
          else 0
      (∫ ω, C b ω ∂P) =
        upBeforeDownExpectation P D.X q (x+ε) (b+ε) +
        downBeforeUpExpectation P D.X q (x+ε) (b+ε) *
          (∫ ω, discountedAt q (reflectedInfExit D.X 0 a ω) ∂P) := by
  sorry
end Kyprianou.Ch08.StageB
