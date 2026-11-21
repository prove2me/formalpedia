-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_avram_stopped_reward
-- name    : Kyprianou.Ch08.StageB.source_result81_uncapped_avram_stopped_reward
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:40:39.634438+00:00
-- url     : https://prove2.me/theorems/4b773ff6-bc13-49fc-b580-51df61b7088d
-- title:
--   Uncapped stopped reward at the lower-killed upper record
-- statement:
--   For a pathwise spectrally negative Lévy model, the unrestricted upper-before-lower stopped payoff is measurable and factors into its discounted historical weight and the mean future-path reward. This is the monotone limit of the existing capped factorization.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, stopped strong Markov argument. Discharges the uncapping step for exact parent 78574f78-b2c0-43ff-a7df-919c061143b7.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_uncapped_avram_stopped_reward
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weight := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoff := fun ω => if U ω < L ω then
      discount (U ω).toNNReal *
        reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω)
      else 0
    Measurable weight ∧ Measurable payoff ∧
      (∫⁻ ω, payoff ω ∂P) = (∫⁻ ω, weight ω ∂P) *
        (∫⁻ ω, reward (fun s => X.X s ω) ∂P) := by
  sorry
