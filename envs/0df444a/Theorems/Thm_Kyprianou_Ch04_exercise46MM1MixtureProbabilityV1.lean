-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1MixtureProbabilityV1
-- name    : Kyprianou.Ch04.exercise46MM1MixtureProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:31:47.080261+00:00
-- url     : https://prove2.me/theorems/99961f4e-1aa1-440b-91e9-74fc2425d929
-- title:
--   Explicit M/M/1 workload mixture has unit mass
-- statement:
--   Integrate the exponential density over the positive half-line; its mass is lambda/(mu-lambda). The prefactor normalises the sum of the atom and density.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MM1MixtureProbabilityV1
    (lambda mu : Real) (hlambda : 0 < lambda) (hmu : lambda < mu) :
    IsProbabilityMeasure
      (ENNReal.ofReal (1 - lambda / mu) •
        ((Measure.dirac (0 : Real)) +
          ((volume : Measure Real).restrict (Ioi 0)).withDensity
            (fun x : Real =>
              ENNReal.ofReal (lambda * Real.exp (-(mu - lambda) * x))))) := by
  sorry
