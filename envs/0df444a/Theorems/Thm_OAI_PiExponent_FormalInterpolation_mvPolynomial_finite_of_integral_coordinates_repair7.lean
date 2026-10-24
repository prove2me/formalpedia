-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_finite_of_integral_coordinates_repair7
-- name    : OAI.PiExponent.FormalInterpolation.mvPolynomial_finite_of_integral_coordinates_repair7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:52:23.215369+00:00
-- url     : https://prove2.me/theorems/ae04ed3f-869e-4cd2-b3de-2520067d2bec
-- title:
--   Integral coordinates imply polynomial module finiteness
-- statement:
--   If every variable in a finite-variable polynomial ring is integral over a subalgebra, the polynomial ring is a finite module over that subalgebra. A proof proceeds by adjoining the variables one at a time; the empty-variable case is included.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib

theorem OAI.PiExponent.FormalInterpolation.mvPolynomial_finite_of_integral_coordinates_repair7
    {d : Nat}
    (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hX : ∀ i : Fin d,
      IsIntegral A (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) :
    Module.Finite A (MvPolynomial (Fin d) Complex) := by sorry
