-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_monomial_quotient_coordinate_class_integral
-- name    : OAI.PiExponent.FormalInterpolation.finite_monomial_quotient_coordinate_class_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:21:25.815284+00:00
-- url     : https://prove2.me/theorems/ee2d5336-8a43-44ba-905b-c8a666959258
-- title:
--   Coordinate class in the finite monomial quotient is integral
-- statement:
--   Each coordinate class is integral over `ℂ`: its specified positive power vanishes in the quotient, so it satisfies a monic polynomial.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_monomial_quotient_coordinate_class_integral (d : Nat) (N : Fin d → Nat) (hN : ∀ i, 0 < N i) (i : Fin d) : IsIntegral ℂ (Ideal.Quotient.mk (Ideal.span (Set.range (fun j : Fin d => (MvPolynomial.X j : MvPolynomial (Fin d) ℂ) ^ N j))) (MvPolynomial.X i)) := by sorry
