-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteEventSumBoundV1
-- name    : Kyprianou.Ch04.exercise41FiniteEventSumBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:42:30.443359+00:00
-- url     : https://prove2.me/theorems/5d7bd186-3a6d-58e4-8de6-35f19ff54988
-- title:
--   Finite-event expected occupancy bound
-- statement:
--   Sum the lower bounds for success probabilities over cells and integrate the pointwise bound of two on the finite sum of successful-cell indicators.
-- source:
--   Kyprianou (2006), Exercise 4.1(i), printed pp.105–106.

import Mathlib

open MeasureTheory Set
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FiniteEventSumBoundV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (I : Finset ℕ) (A B : ℕ → Set Ω) (p : ℝ≥0∞)
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (hfactor : ∀ i ∈ I, p * P (A i) ≤ P (B i))
    (hbound : ∀ ω, ∑ i ∈ I,
      (B i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω ≤ 2) :
    p * ∑ i ∈ I, P (A i) ≤ 2 := by
  sorry
