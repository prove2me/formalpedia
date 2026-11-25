-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ServiceTrafficRatioV1
-- name    : Kyprianou.Ch04.exercise46ServiceTrafficRatioV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T09:55:02.633671+00:00
-- url     : https://prove2.me/theorems/83861abb-d2c9-5502-8f4c-34eb3372dac5
-- title:
--   Exercise 4.6(ii): service mean implies overloaded jump-magnitude intensity
-- statement:
--   For a positive service law, arrival intensity times the mean service duration above one implies the corresponding negative-mark Lévy measure has jump-magnitude intensity above one.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6(ii), service-law change of variables.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46ServiceTrafficRatioV1
    (service : Measure Real) [IsProbabilityMeasure service]
    (hPositive : service (Ioi (0 : Real)) = 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (nu : Measure Real)
    (hInput : nu = ENNReal.ofReal lambda • service.map (fun x : Real => -x))
    (hOverload : 1 < lambda * ∫ y : Real, y ∂service) :
    1 < ∫⁻ y : Real, ENNReal.ofReal (-y) ∂nu := by
  sorry
