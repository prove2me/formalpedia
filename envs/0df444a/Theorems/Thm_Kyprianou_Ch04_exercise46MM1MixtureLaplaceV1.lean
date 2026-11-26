-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1MixtureLaplaceV1
-- name    : Kyprianou.Ch04.exercise46MM1MixtureLaplaceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:40:28.363955+00:00
-- url     : https://prove2.me/theorems/efabdca5-a707-4269-9eed-fa2e0e8d4d2a
-- title:
--   Laplace transform of explicit stationary M/M/1 mixture
-- statement:
--   Laplace transform of explicit stationary M/M/1 mixture.
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46ExponentialDensityLaplaceV1
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MM1MixtureLaplaceV1
    (lambda mu s : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu) (hs : 0 ≤ s) :
    let m : Measure Real := ENNReal.ofReal (1-lambda/mu) •
      ((Measure.dirac (0 : Real)) +
        ((volume : Measure Real).restrict (Ioi 0)).withDensity
          (fun x => ENNReal.ofReal
            (lambda*Real.exp (-(mu-lambda)*x))))
    (∫⁻ x, ENNReal.ofReal (Real.exp (-s*x)) ∂m) =
      ENNReal.ofReal ((1-lambda/mu)*(1+lambda/(mu-lambda+s))) := by
  sorry
