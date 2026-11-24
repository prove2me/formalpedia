-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_reset_sandwich
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_reset_sandwich
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:05:06.611248+00:00
-- url     : https://prove2.me/theorems/d4357884-ba43-4859-9ee6-44842f39b0ad
-- title:
--   Actual lower-reflected exit sandwiched by epsilon-reset renewal quotients
-- statement:
--   Reset the reference infimum only when the current increment falls strictly more than epsilon below the previous reset level, taking the overshoot as the new reference. The approximate reflected height is at most the actual height and differs by at most epsilon until the next reset. Its two-sided upper/lower cycles have geometric renewal transform R(epsilon,b), from the original two-sided exit identities. Thus the actual exit discount lies between the transforms for b=a and b=a-epsilon whenever the latter starts above the initial height. Every discount is bounded by one.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii); Pistorius (2004), Proposition 2(i), and two-sided exit renewal approximation.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Actual lower-reflected exit sandwiched by epsilon-reset renewal quotients -/
theorem p2m810_inf_reset_sandwich :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      let R := fun (ε b : ℝ) => ((Zscale q (W q) (x+ε) -
        W q (x+ε) * ((Zscale q (W q) ε - 1) / W q ε)) /
      (Zscale q (W q) (b+ε) -
        W q (b+ε) * ((Zscale q (W q) ε - 1) / W q ε)))
      let F := ∫ ω, discountedAt q (reflectedInfExit D.X x a ω) ∂P
      F ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < a →
        R ε a ≤ F ∧ (x ≤ a - ε → F ≤ R ε (a-ε)) := by
  sorry
end Kyprianou.Ch08.StageB
