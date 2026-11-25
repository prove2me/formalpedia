-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_null_right_local_intervals
-- name    : Kyprianou.Ch04.kw47_null_right_local_intervals
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:39:51.795864+00:00
-- url     : https://prove2.me/theorems/e457cb42-79c2-450c-8862-002544a6420f
-- title:
--   Atomless measure of right-locally null points
-- statement:
--   Select a rational right endpoint in each witness interval, and use countable subadditivity and the fixed-right-endpoint null set.
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 320-321; continuous Stieltjes product calculus.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_null_right_local_intervals
    (mu : Measure Real) [NullSingletonClass mu] :
    mu {x : Real | ∃ y : Real, x < y ∧ mu (Ioc x y) = 0} = 0 := by sorry
