-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_stopped_payoff_occupation
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_factor_stopped_payoff_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T04:25:44.124401+00:00
-- url     : https://prove2.me/theorems/ee0147bb-3081-4409-86c6-bbfddc4c9b01
-- title:
--   Discounted stopped payoff equals upper-exit occupation
-- statement:
--   The ENNReal discounted reward paid at the lower-killed upper passage equals the positive-time integral of the upper-exit occupation probability, using the random time-shift identity and strict clock transfer.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem Kyprianou.Ch08.StageB.p2m87_qpos_factor_stopped_payoff_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a x : ℝ) (hq : 0 < q) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a)
    (A : Set ℝ) (hA : MeasurableSet A)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hreward : Measurable reward)
    (hreward_value : ∀ (y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) → y 0 = 0 →
        reward y =
          (∫⁻ s : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
            (if (s : WithTop ℝ≥0) <
                  tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧
                a + y s ∈ A
             then (1 : ℝ≥0∞) else 0) ∂positiveTimeLebesgue)) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    (∫⁻ ω, if U ω < L ω then disc (τ ω) *
        reward (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
      ∫⁻ t : ℝ≥0, disc t *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
          shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue
:= by
  sorry
