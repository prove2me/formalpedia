-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_exp_remainder
-- name    : Kyprianou.Ch04.kw48_exp_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:25:51.354799+00:00
-- url     : https://prove2.me/theorems/06720d64-e60d-5758-a624-ddbde43bf951
-- title:
--   Small complex exponential quadratic remainder
-- statement:
--   Small complex exponential quadratic remainder.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i), complex product-grid proof.

import Mathlib
set_option autoImplicit false

/-- Quadratic error in the small complex exponential increment. -/

theorem Kyprianou.Ch04.kw48_exp_remainder (z : Complex) (hz : ‖z‖ ≤ 1) :
    ‖1 - Complex.exp (-z) - z‖ ≤ ‖z‖ ^ 2 := by sorry
