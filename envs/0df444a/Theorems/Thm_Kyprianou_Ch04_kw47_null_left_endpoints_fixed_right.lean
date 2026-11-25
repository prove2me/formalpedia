-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_null_left_endpoints_fixed_right
-- name    : Kyprianou.Ch04.kw47_null_left_endpoints_fixed_right
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:39:52.721833+00:00
-- url     : https://prove2.me/theorems/4b7fc236-b6d4-47bc-b06a-3b402371c6b6
-- title:
--   Null set of left endpoints of null intervals
-- statement:
--   For a fixed right endpoint, rational coinitial choices of left endpoints give countably many null intervals; the remaining possible minimum is a null singleton.
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 320-321; continuous Stieltjes product calculus.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_null_left_endpoints_fixed_right
    (mu : Measure Real) [NullSingletonClass mu] (q : Real) :
    mu {x : Real | x < q ∧ mu (Ioc x q) = 0} = 0 := by sorry
