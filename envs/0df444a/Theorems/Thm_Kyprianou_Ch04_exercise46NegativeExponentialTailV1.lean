-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46NegativeExponentialTailV1
-- name    : Kyprianou.Ch04.exercise46NegativeExponentialTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:57:38.180417+00:00
-- url     : https://prove2.me/theorems/49563f27-4505-59b9-9780-dadc4b641779
-- title:
--   Tail of the negative exponential Lévy density
-- statement:
--   Restrict to the negative tail and use the exponential integral on the negative half-line.
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46NegativeExponentialTailV1
    (lambda mu : Real) (hlambda : 0 < lambda) (hmu : 0 < mu)
    (x : Real) (hx : 0 ≤ x) :
    (((volume : Measure Real).restrict (Iio 0)).withDensity
      (fun y => ENNReal.ofReal (lambda * mu * Real.exp (mu*y)))) (Iio (-x)) =
      ENNReal.ofReal (lambda * Real.exp (-mu*x)) := by
  sorry
