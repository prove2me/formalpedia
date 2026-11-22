-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_real_avram_stopped_reward_integrable
-- name    : Kyprianou.Ch08.StageB.source_result81_uncapped_real_avram_stopped_reward_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T04:02:22.803343+00:00
-- url     : https://prove2.me/theorems/2f3b7235-e6fa-4f67-b6dd-62e07327c32c
-- title:
--   Integrability of bounded uncapped stopped reward and weights
-- statement:
--   For measurable [0,1]-bounded discounts and future-path rewards, the upper-before-lower stopped payoff, its historical weight, and the ordinary future-path reward are all integrable on a probability space. Helper isolating measurability and L1 bounds for the bounded-real stopped reward factorization 16d2c69d.
-- source:
--   Helper for Kyprianou Ch08 StageB 16d2c69d bounded-real stopped reward factorization; isolates [0,1] measurability and integrability for complexity-gate split.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_uncapped_real_avram_stopped_reward_integrable
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount) (hdb : ∀ t, 0 ≤ discount t ∧ discount t ≤ 1)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) (hrb : ∀ f, 0 ≤ reward f ∧ reward f ≤ 1) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weight := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoff := fun ω => if U ω < L ω then discount (U ω).toNNReal * reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω) else 0
    Integrable payoff P ∧ Integrable weight P ∧ Integrable (fun ω => reward (fun s => X.X s ω)) P := by
  sorry
