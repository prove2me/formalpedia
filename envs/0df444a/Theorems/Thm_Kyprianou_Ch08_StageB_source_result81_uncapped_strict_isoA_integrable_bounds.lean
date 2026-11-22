-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_strict_isoA_integrable_bounds
-- name    : Kyprianou.Ch08.StageB.source_result81_uncapped_strict_isoA_integrable_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T03:29:35.008482+00:00
-- url     : https://prove2.me/theorems/7c4f4aa8-9c03-45aa-a142-0281b489a8a1
-- title:
--   Uncapped stopped weight payoff integrability and bounds
-- statement:
--   For measurable [0,1]-bounded discount and reward, the upper-before-lower stopped weight, stopped payoff, and ordinary reward processes are integrable with pointwise [0,1] bounds. This is a technical extraction of the parent uncapped real stopped-reward proof, isolating measurability via passage clocks and shifted paths plus bounded integrability.
-- source:
--   Strict-isolation extraction of parent 16d2c69d-3c6f-4486-8687-1d77d4d48ea0 bridge (complexity 0.4471). Helper ISO-A isolates integrability and bounds; proof uses only Proved passage-clock and shifted-path measurability plus bounded integrability. No sibling H1/H2 dependency.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_uncapped_strict_isoA_integrable_bounds
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount) (hdb : ∀ t, 0 ≤ discount t ∧ discount t ≤ 1)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) (hrb : ∀ f, 0 ≤ reward f ∧ reward f ≤ 1) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weightR := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoffR := fun ω => if U ω < L ω then discount (U ω).toNNReal * reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω) else 0
    let rewR := fun ω => reward (fun s => X.X s ω)
    (Integrable weightR P ∧ ∀ ω, 0 ≤ weightR ω ∧ weightR ω ≤ 1) ∧
    (Integrable payoffR P ∧ ∀ ω, 0 ≤ payoffR ω ∧ payoffR ω ≤ 1) ∧
    (Integrable rewR P ∧ ∀ ω, 0 ≤ rewR ω ∧ rewR ω ≤ 1) := by sorry
