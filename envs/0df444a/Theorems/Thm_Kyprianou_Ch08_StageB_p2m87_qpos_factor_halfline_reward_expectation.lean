-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_halfline_reward_expectation
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_factor_halfline_reward_expectation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T04:25:43.155733+00:00
-- url     : https://prove2.me/theorems/c10d6b1b-76ad-4362-ba37-2e3494ffe479
-- title:
--   Half-line occupation reward expectation is a time integral
-- statement:
--   For a measurable occupation reward of a right-continuous path starting at the upper level, the expectation of the reward on the Avram path equals the discounted time integral of the source half-line occupation probability.

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

theorem Kyprianou.Ch08.StageB.p2m87_qpos_factor_halfline_reward_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hreward : Measurable reward)
    (hreward_value : ∀ (y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) → y 0 = 0 →
        reward y =
          (∫⁻ s : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
            (if (s : WithTop ℝ≥0) <
                  tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧
                a + y s ∈ A
             then (1 : ℝ≥0∞) else 0) ∂positiveTimeLebesgue)) :
    (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) =
      ∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
          shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue
:= by
  sorry
