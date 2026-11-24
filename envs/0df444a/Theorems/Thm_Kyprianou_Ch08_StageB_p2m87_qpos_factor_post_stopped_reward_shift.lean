-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_post_stopped_reward_shift
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_factor_post_stopped_reward_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T04:25:46.453796+00:00
-- url     : https://prove2.me/theorems/bdfc1113-10d9-4f2e-a33c-6f312b12f7d7
-- title:
--   Post-upper-exit occupation reward is the shifted occupation integrand
-- statement:
--   On the upper-before-lower exit event, no positive jumps gives an exact passage level; translating the strict lower clock turns the stopped occupation reward into the discounted occupation integrand evaluated after the stopping time.

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

theorem Kyprianou.Ch08.StageB.p2m87_qpos_factor_post_stopped_reward_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (q a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a)
    (A : Set ℝ) (hA : MeasurableSet A)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hreward_value : ∀ (y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) → y 0 = 0 →
        reward y =
          (∫⁻ s : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
            (if (s : WithTop ℝ≥0) <
                  tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧
                a + y s ∈ A
             then (1 : ℝ≥0∞) else 0) ∂positiveTimeLebesgue))
    (ω : Ω)
    (hUL : twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    let R : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
      if U ω < L ω then disc t *
        (if (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A then 1 else 0) else 0
    disc (τ ω) * reward (fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) =
      ∫⁻ s : ℝ≥0, R (τ ω + s) ω ∂positiveTimeLebesgue
:= by
  sorry
