-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_exponential_cell_product
-- name    : Kyprianou.Ch04.kw47_exponential_cell_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:39:53.92032+00:00
-- url     : https://prove2.me/theorems/2b1a3b3f-f2da-4585-b0be-6cfa9c70d14d
-- title:
--   Exact exponential product cell identity
-- statement:
--   Factor the right-endpoint exponential product in each cell, exposing the exponent of the running-supremum increment and time increment.
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 320-321; continuous Stieltjes product calculus.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_exponential_cell_product
    (alpha psi xa xb ua ub a b : Real) :
    Real.exp (alpha * xb - psi * b) *
        (Real.exp (-alpha * ub + psi * b) - Real.exp (-alpha * ua + psi * a)) =
      Real.exp (-alpha * (ub - xb)) *
        (1 - Real.exp (alpha * (ub - ua) - psi * (b - a))) := by sorry
