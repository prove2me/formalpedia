-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FiniteLawCDFTransformV1
-- name    : Kyprianou.Ch04.exercise46FiniteLawCDFTransformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T21:08:34.504937+00:00
-- url     : https://prove2.me/theorems/c5fe4b05-3f16-48c2-8659-4f35c1614ed4
-- title:
--   Exponential CDF integral for a finite nonnegative measure
-- statement:
--   Apply the established positive cumulative measure Laplace identity and convert between nonnegative and real integrals. No normalisation of the finite measure is required.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FiniteLawCDFTransformV1
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hsupp : nu (Iio (0 : Real)) = 0)
    (beta : Real) (hb : 0 < beta) :
    beta * (∫ t in Ici (0 : Real),
      Real.exp (-beta * t) * (nu (Iic t)).toReal ∂volume) =
      ∫ y, Real.exp (-beta * y) ∂nu := by
  sorry
