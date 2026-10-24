-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_X_pow_weightedHomogeneous
-- name    : OAI.PiExponent.FormalInterpolation.X_pow_weightedHomogeneous
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:05:28.836676+00:00
-- url     : https://prove2.me/theorems/6928000c-b795-4a24-8a61-f5a23d5bda90
-- title:
--   A coordinate power is weighted homogeneous
-- statement:
--   The monomial X_i^n has weighted degree n times the weight of coordinate i. This includes n = 0, where the polynomial is 1 of degree zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.X_pow_weightedHomogeneous
    {d : Nat} (w : Fin d → Rat) (i : Fin d) (n : Nat) :
    ((MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n).IsWeightedHomogeneous
      (fun l => (w l : Real)) ((n : Real) * (w i : Real)) := by sorry
