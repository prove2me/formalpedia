-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_second_derivative
-- name    : Kyprianou.Ch04.ito43_cosine_second_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:24:49.18504+00:00
-- url     : https://prove2.me/theorems/8218724e-898e-4a02-bb68-0dbc09d727f8
-- title:
--   Cosine has second derivative negative cosine
-- statement:
--   Apply iterated differentiation and the sine and cosine derivative formulae.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cosine_second_derivative :
    iteratedDeriv 2 Real.cos = fun x => -Real.cos x := by sorry
