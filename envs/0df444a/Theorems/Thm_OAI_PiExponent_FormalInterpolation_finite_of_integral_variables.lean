-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_of_integral_variables
-- name    : OAI.PiExponent.FormalInterpolation.finite_of_integral_variables
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:26:40.749571+00:00
-- url     : https://prove2.me/theorems/30e3419f-57fe-4886-81be-7be7aae383ff
-- title:
--   Integral polynomial variables imply module finiteness
-- statement:
--   If every variable is integral over the subalgebra A, adjoining the finitely many variables successively makes the polynomial ring a finite A-module. The variables generate the polynomial ring over Complex, and the result includes d = 0.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib

theorem OAI.PiExponent.FormalInterpolation.finite_of_integral_variables
    {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hvars : ∀ i : Fin d, IsIntegral A (MvPolynomial.X (R := Complex) i)) :
    Module.Finite A (MvPolynomial (Fin d) Complex) := by sorry
