-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveDiscountSequenceAndClockError
-- name    : Kyprianou.Ch04.positiveDiscountSequenceAndClockError
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:39:40.564933+00:00
-- url     : https://prove2.me/theorems/a2afc91c-5cd4-54e5-b753-e3eb7e053f6f
-- title:
--   Positive discount sequence and vanishing clock error
-- statement:
--   The reciprocal sequence of shifted naturals tends to zero, and continuity of the exponential gives the early-clock error limit.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveDiscountSequenceAndClockError :
    let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    (∀ n, 0 < q n) ∧ Tendsto q atTop (nhds 0) ∧
      ∀ T : NNReal, Tendsto (fun n => 1 - Real.exp (-(q n * (T : ℝ)))) atTop (nhds 0) := by
  sorry
