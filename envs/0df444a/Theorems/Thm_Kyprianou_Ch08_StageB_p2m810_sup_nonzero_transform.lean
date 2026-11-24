-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_nonzero_transform
-- name    : Kyprianou.Ch08.StageB.p2m810_sup_nonzero_transform
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:12:38.821809+00:00
-- url     : https://prove2.me/theorems/aaab97eb-34d6-4ee7-9e02-8cefdab5c2e1
-- title:
--   Reflected joint payoff for nonzero denominator
-- statement:
--   Apply the stopped Z-scale balance and the discounted record formula; the denominator is the tilted untilted derivative.
-- source:
--   Kyprianou (2006), Theorem 8.10.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Reflected joint payoff for nonzero denominator -/
theorem p2m810_sup_nonzero_transform :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q θ x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      Integrable (fun ω => Real.exp (θ * D.X 1 ω)) P →
      let p := q - ψ θ
      let V := tiltedScale θ (W q)
      let Zv := Zscale p V
      let d := derivWithin V (Ici a) a
      d + θ * V a ≠ 0 →
      (∫ ω, reflectedSupJointPayoff D.X q θ x a ω ∂P) =
        Real.exp (-θ*x) * (Zv (a-x) -
          V (a-x) * (p * V a + θ * Zv a) / (d + θ * V a)) := by
  sorry
end Kyprianou.Ch08.StageB
