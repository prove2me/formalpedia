-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MM1GeometricMixtureIdentityV1
-- name    : Kyprianou.Ch04.exercise46MM1GeometricMixtureIdentityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:58:53.916273+00:00
-- url     : https://prove2.me/theorems/b6ff470d-93cd-5339-b064-fd3e50e28a48
-- title:
--   Geometric convolution law for exponential services equals explicit M/M/1 mixture
-- statement:
--   Identify the two probability measures by their negative Laplace transforms. The geometric series sums to the same atom-plus-exponential transform.
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MM1GeometricMixtureIdentityV1
    (lambda mu : Real) (hlambda : 0 < lambda) (hmu : lambda < mu)
    (nu eta : Measure Real) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (heta : eta = ((volume : Measure Real).restrict (Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (mu*Real.exp (-mu*x))))
    (hLaw : ∀ B : Set Real, MeasurableSet B →
      nu B = ∑' n : Nat,
        ((1-ENNReal.ofReal (lambda/mu)) * ENNReal.ofReal (lambda/mu)^n) *
        ((Nat.rec (Measure.dirac (0 : Real)) (fun _ (m : Measure Real) => m.conv eta) n : Measure Real) B)) :
    nu = ENNReal.ofReal (1-lambda/mu) •
      ((Measure.dirac (0 : Real)) +
        ((volume : Measure Real).restrict (Ioi 0)).withDensity
          (fun x => ENNReal.ofReal (lambda*Real.exp (-(mu-lambda)*x)))) := by
  sorry
