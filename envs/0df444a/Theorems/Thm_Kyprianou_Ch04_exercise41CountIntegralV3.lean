-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41CountIntegralV3
-- name    : Kyprianou.Ch04.exercise41CountIntegralV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:06:10.161951+00:00
-- url     : https://prove2.me/theorems/6d85e995-9726-53d3-a41e-44740b764c22
-- title:
--   Measurable finite occupancy count has integral equal to sum of event probabilities
-- statement:
--   Measurable finite occupancy count has integral equal to sum of event probabilities
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41CountIntegralV3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Finset ℕ) (A : ℕ → Set Ω)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ∑ i ∈ I, (A i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω
    Measurable N ∧ (∫⁻ ω, N ω ∂P) = ∑ i ∈ I, P (A i)  := by
  sorry
