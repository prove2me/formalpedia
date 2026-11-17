-- Prove2me | Theorems.Thm_Kyprianou_Ch06_poissonZeroCountAsExponential
-- name    : Kyprianou.Ch06.poissonZeroCountAsExponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:01:20.577049+00:00
-- url     : https://prove2.me/theorems/a3d6d43a-31d2-4893-9bec-c56c93b1fd61
-- title:
--   Chapter 6 Poisson zero-count probability is an exponential
-- statement:
--   For a Poisson random variable of intensity rate × time, probability of zero counts is exp(-rate × time). This exact identity uses the pinned Mathlib Poisson singleton measure and is used to identify the fixed-time first-arrival survival function.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.poissonZeroCountAsExponential
    (rate t : NNReal) :
    ProbabilityTheory.poissonMeasure (t * rate) {0} =
      ENNReal.ofReal
        (Real.exp (-((rate : Real) * (t : Real)))) := by sorry
