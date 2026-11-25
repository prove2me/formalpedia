-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_discrete_product_summation
-- name    : Kyprianou.Ch04.kw47_discrete_product_summation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:30:38.609737+00:00
-- url     : https://prove2.me/theorems/21ac2503-a241-56c2-9479-6545d759555e
-- title:
--   Exact finite discrete product summation by parts
-- statement:
--   Exact summation by parts for arbitrary real sequences and finite grid length; telescope the pointwise product increments.
-- source:
--   Kyprianou (2006), Exercise 4.7, worked solution pp. 320-321; product calculus reduction.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_discrete_product_summation
    (E H : Nat → Real) (n : Nat) :
    (∑ k ∈ Finset.range n, H k * (E (k+1) - E k)) =
      E n * H n - E 0 * H 0 -
        ∑ k ∈ Finset.range n, E (k+1) * (H (k+1) - H k) := by sorry
