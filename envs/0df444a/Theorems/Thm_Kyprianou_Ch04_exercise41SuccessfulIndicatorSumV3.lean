-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulIndicatorSumV3
-- name    : Kyprianou.Ch04.exercise41SuccessfulIndicatorSumV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:39:33.471155+00:00
-- url     : https://prove2.me/theorems/0c4adc06-d4cc-52d2-aecf-c7b49e105c48
-- title:
--   Successful-cell indicator sum equals filtered cardinality
-- statement:
--   Successful-cell indicator sum equals filtered cardinality
-- source:
--   Kyprianou (2006), Exercise 4.1(i), finite-grid proof.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SuccessfulIndicatorSumV3
    {Ω : Type} (I : Finset ℕ) (B : ℕ → Set Ω) (ω : Ω) :
    (∑ i ∈ I, (B i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω) =
      ((I.filter (fun i => ω ∈ B i)).card : ℝ≥0∞)  := by
  sorry
