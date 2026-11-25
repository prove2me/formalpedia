-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1TrafficIntegratedTailV1
-- name    : Kyprianou.Ch04.exercise46MM1TrafficIntegratedTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:58:57.569407+00:00
-- url     : https://prove2.me/theorems/f37f01c4-e8fe-4e6f-b70d-ceb99145390c
-- title:
--   Exponential service traffic and normalised integrated Lévy tail
-- statement:
--   Use the negative exponential tail and layer-cake identity. Integrate the tail and divide by the traffic ratio.
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MM1TrafficIntegratedTailV1
    (lambda mu : Real) (hlambda : 0 < lambda) (hmu : lambda < mu)
    (nu : Measure Real)
    (hnu : nu = ((volume : Measure Real).restrict (Iio 0)).withDensity
      (fun y => ENNReal.ofReal (lambda*mu*Real.exp (mu*y)))) :
    let rho := ∫⁻ y : Real, ENNReal.ofReal (-y) ∂nu
    rho = ENNReal.ofReal (lambda/mu) ∧
      ((volume : Measure Real).restrict (Ioi 0)).withDensity
        (fun x => nu (Iio (-x)) / rho) =
      ((volume : Measure Real).restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (mu*Real.exp (-mu*x))) := by
  sorry
