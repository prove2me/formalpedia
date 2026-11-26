-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1DrawdownRationalV1
-- name    : Kyprianou.Ch04.exercise46MM1DrawdownRationalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:26:30.741519+00:00
-- url     : https://prove2.me/theorems/5df4f4a1-9c21-4dac-8506-974ff97e0eb1
-- title:
--   M/M/1 positive-drift transform cancellation
-- statement:
--   M/M/1 positive-drift transform cancellation
-- source:
--   Kyprianou (2006), Exercise 4.6.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MM1DrawdownRationalV1
    (lambda mu beta : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hbeta : 0 < beta) :
    (1-lambda/mu)*beta / (beta-lambda*beta/(mu+beta)) =
      (1-lambda/mu)*(1+lambda/(mu-lambda+beta)) := by
  sorry
