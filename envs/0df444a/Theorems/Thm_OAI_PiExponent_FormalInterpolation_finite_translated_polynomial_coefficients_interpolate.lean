-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_translated_polynomial_coefficients_interpolate
-- name    : OAI.PiExponent.FormalInterpolation.finite_translated_polynomial_coefficients_interpolate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T21:14:52.223988+00:00
-- url     : https://prove2.me/theorems/14a93359-dfaa-45aa-9760-fe5e08819730
-- title:
--   Finite Taylor coefficients interpolate independently at distinct points
-- statement:
--   At finitely many distinct points of complex affine space, an unrestricted multivariate polynomial can realize arbitrary prescribed Taylor coefficients indexed by any finite family of distinct monomials. Empty index sets are allowed, and no downward-closure assumption on the monomial family is needed.

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic

theorem OAI.PiExponent.FormalInterpolation.finite_translated_polynomial_coefficients_interpolate
    {n : Nat} {J A : Type} [Fintype J] [Fintype A]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (e : A → (Fin n →₀ Nat)) (he : Function.Injective e)
    (y : J × A → Complex) :
    ∃ Q : MvPolynomial (Fin n) Complex, ∀ (j : J) (a : A),
      (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.C (c j i) + MvPolynomial.X i) Q).coeff
          (e a) = y (j, a) := by sorry
