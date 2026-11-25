-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ServiceLaplaceBoundsV1
-- name    : Kyprianou.Ch04.exercise46ServiceLaplaceBoundsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T10:24:06.410121+00:00
-- url     : https://prove2.me/theorems/803adef5-1478-48da-ace0-ef7c20329481
-- title:
--   Positive service marks have a strictly interior Laplace transform
-- statement:
--   Under a positive service probability law and a strictly positive transform argument, the service Laplace transform lies strictly between zero and one.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6(ii).

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46ServiceLaplaceBoundsV1
    (service : Measure Real) [IsProbabilityMeasure service]
    (hPositive : service (Ioi (0 : Real)) = 1)
    (phi : Real) (hphi : 0 < phi) :
    0 < (∫ y : Real, Real.exp (-phi * y) ∂service) ∧
      (∫ y : Real, Real.exp (-phi * y) ∂service) < 1 := by
  sorry
