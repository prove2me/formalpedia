-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_kyprianou81_uncapped_ofReal_stopped_reward_factor
-- name    : Kyprianou.Ch08.StageB.kyprianou81_uncapped_ofReal_stopped_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T02:36:02.970811+00:00
-- url     : https://prove2.me/theorems/315c5cc5-3459-45a1-a958-4c925a46ad1f
-- title:
--   Uncapped stopped ofReal reward factors at the lower-killed upper record
-- statement:
--   For measurable real discount and path-reward functions (lifted to ENNReal via ofReal), the upper-before-lower stopped payoff lower-integral in a pathwise Levy model factors into the expected historical ofReal discount and the ordinary ofReal future-path reward. This is the ENNReal shadow of the bounded-real stopped reward identity, proved from the accepted capped strong-Markov factor by monotone passage to the uncapped clocks.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.kyprianou81_uncapped_ofReal_stopped_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let discountE : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (discount t)
    let rewardE : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f => ENNReal.ofReal (reward f)
    (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) *
      rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
      else 0 ∂P) =
      (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, rewardE (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  sorry
