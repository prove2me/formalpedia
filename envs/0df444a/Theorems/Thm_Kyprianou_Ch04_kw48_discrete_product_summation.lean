-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_discrete_product_summation
-- name    : Kyprianou.Ch04.kw48_discrete_product_summation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:25:54.354264+00:00
-- url     : https://prove2.me/theorems/75ebbe5d-506a-41d2-88a3-075fd70cc603
-- title:
--   Complex discrete product summation by parts
-- statement:
--   Complex discrete product summation by parts.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i), complex product-grid proof.

import Mathlib
set_option autoImplicit false

/-- Discrete integration by parts for complex-valued sequences. -/

theorem Kyprianou.Ch04.kw48_discrete_product_summation (E H : Nat → Complex) (N : Nat) :
    (∑ i ∈ Finset.range N, H i * (E (i+1) - E i)) +
    (∑ i ∈ Finset.range N, E (i+1) * (H (i+1) - H i)) =
      E N * H N - E 0 * H 0 := by sorry
