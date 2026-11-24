-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_joint_scale_balance
-- name    : Kyprianou.Ch08.StageB.p2m810_sup_joint_scale_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:05:06.823633+00:00
-- url     : https://prove2.me/theorems/79aba251-783c-4636-9247-2dcb9d1e2b76
-- title:
--   Stopped reflected two-parameter Z-scale balance with discounted record regulator
-- statement:
--   The generalised Z harmonic function, applied to the upper-reflected surplus a minus drawdown, has initial value minus the upper regulator contribution. At the strict exit the terminal scale equals the actual exponential payoff. The regulator is represented by integration of discounted record crossing probabilities. Use the stopped harmonic identity and localised change of variables, or record-level renewal and limiting compensation.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); Avram, Kyprianou and Pistorius (2004), section 4, equations (13)-(22).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Stopped reflected two-parameter Z-scale balance with discounted record regulator -/
theorem p2m810_sup_joint_scale_balance :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q θ x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      Integrable (fun ω => Real.exp (θ * D.X 1 ω)) P →
      derivWithin (W q) (Ici a) a ≠ 0 →
      let p := q - ψ θ
      let V := tiltedScale θ (W q)
      let Zv := Zscale p V
      (∫ ω, reflectedSupJointPayoff D.X q θ x a ω ∂P) =
        Real.exp (-θ*x) * Zv (a-x) -
          (p * V a + θ * Zv a) *
          (∫ l in Ioi x, ∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X x a ω
          then discountedAt q (tauPlus D.X l ω) else 0 ∂P) := by
  sorry
end Kyprianou.Ch08.StageB
