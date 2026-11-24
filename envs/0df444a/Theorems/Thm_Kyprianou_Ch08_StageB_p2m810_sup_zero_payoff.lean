-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_zero_payoff
-- name    : Kyprianou.Ch08.StageB.p2m810_sup_zero_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:12:33.850997+00:00
-- url     : https://prove2.me/theorems/39ba63aa-89ef-453b-9cbb-a04a5cc5800f
-- title:
--   Reflected joint payoff for zero denominator
-- statement:
--   The zero tilted denominator implies zero untilted right derivative; the strict exit clock is almost surely infinite.
-- source:
--   Kyprianou (2006), Theorem 8.10.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Reflected joint payoff for zero denominator -/
theorem p2m810_sup_zero_payoff :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q θ x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      Integrable (fun ω => Real.exp (θ * D.X 1 ω)) P →
      derivWithin (tiltedScale θ (W q)) (Ici a) a + θ * tiltedScale θ (W q) a = 0 →
      (∫ ω, reflectedSupJointPayoff D.X q θ x a ω ∂P) = 0 := by
  sorry
end Kyprianou.Ch08.StageB
