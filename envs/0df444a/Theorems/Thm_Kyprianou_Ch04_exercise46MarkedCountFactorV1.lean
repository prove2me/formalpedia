-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MarkedCountFactorV1
-- name    : Kyprianou.Ch04.exercise46MarkedCountFactorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:26:29.935927+00:00
-- url     : https://prove2.me/theorems/912def8a-aba1-5f7d-95a9-0d228a634352
-- title:
--   Eliminate common predictable-clock factor
-- statement:
--   Eliminate common predictable-clock factor
-- source:
--   Kyprianou (2006), Exercise 4.6.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MarkedCountFactorV1
    (a b clock rate mark : ENNReal)
    (ha : a = clock * rate)
    (hb : b = clock * (rate * mark)) :
    b = a * mark := by
  sorry
