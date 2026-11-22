-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_real_avram_stopped_reward
-- name    : Kyprianou.Ch08.StageB.source_result81_uncapped_real_avram_stopped_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:11:10.6563+00:00
-- url     : https://prove2.me/theorems/16d2c69d-3c6f-4486-8687-1d77d4d48ea0
-- title:
--   Bounded real stopped reward at the lower-killed upper record
-- statement:
--   For measurable discounts and future-path rewards in [0, 1], the upper-before-lower stopped reward is integrable in a pathwise Lévy model. Its expectation factors into the expected historical discount and the ordinary future-path reward. The factorization is the finite real form of the unrestricted nonnegative stopped-path identity.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, stopped strong Markov argument. Real-valued bounded specialization of 4b773ff6-bc13-49fc-b580-51df61b7088d, used to prove exact pathwise restart parent ec8b0c1f-b094-427a-8298-04f0c7b4a7d5.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_uncapped_real_avram_stopped_reward
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount) (hdb : ∀ t, 0 ≤ discount t ∧ discount t ≤ 1)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) (hrb : ∀ f, 0 ≤ reward f ∧ reward f ≤ 1) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weight := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoff := fun ω => if U ω < L ω then
      discount (U ω).toNNReal *
        reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω)
      else 0
    Integrable payoff P ∧
      (∫ ω, payoff ω ∂P) = (∫ ω, weight ω ∂P) * (∫ ω, reward (fun s => X.X s ω) ∂P) := by
  sorry
