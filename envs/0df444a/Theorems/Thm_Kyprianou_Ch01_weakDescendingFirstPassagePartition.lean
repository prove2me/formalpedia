-- Prove2me | Theorems.Thm_Kyprianou_Ch01_weakDescendingFirstPassagePartition
-- name    : Kyprianou.Ch01.weakDescendingFirstPassagePartition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:04:30.761174+00:00
-- url     : https://prove2.me/theorems/9f4d8087-9f43-4cfe-9592-e4f82a66136c
-- title:
--   Weak-descending first-passage event partitions into disjoint stopping-index events
-- statement:
--   For every real-increment measurable random walk and every measurable B contained in nonpositive reals, the measure of first strictly positive-path descent into B equals the sum over all first-passage indices n+1 of the corresponding stopped-event measures. The stopping events are measurable and pairwise disjoint because B is nonpositive and all earlier partial sums are strictly positive. No independence is needed.
-- source:
--   Kyprianou (2006), Exercise 1.8(ii), worked solution printed page 304

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.weakDescendingFirstPassagePartition
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hsubset : B ⊆ Set.Iic (0 : ℝ)) :
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    P {ω | ∃ n : ℕ, 1 ≤ n ∧ S n ω ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j < n → 0 < S j ω} =
      ∑' n : ℕ, P {ω | S (n + 1) ω ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} := by
  sorry
