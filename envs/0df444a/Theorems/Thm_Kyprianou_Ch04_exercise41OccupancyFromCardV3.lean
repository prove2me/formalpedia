-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41OccupancyFromCardV3
-- name    : Kyprianou.Ch04.exercise41OccupancyFromCardV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:06:10.155304+00:00
-- url     : https://prove2.me/theorems/0edb3373-5b7f-56f9-bf8d-b3b1826bf9d9
-- title:
--   Successful-cell cardinality and restart factorisation imply occupancy sum bound
-- statement:
--   Successful-cell cardinality and restart factorisation imply occupancy sum bound
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41OccupancyFromCardV3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : Finset ℕ) (A B : ℕ → Set Ω) (p : ℝ≥0∞)
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (hfactor : ∀ i ∈ I, p * P (A i) ≤ P (B i))
    (hcard : ∀ ω, (I.filter (fun i => ω ∈ B i)).card ≤ 2) :
    p * ∑ i ∈ I, P (A i) ≤ 2  := by
  sorry
