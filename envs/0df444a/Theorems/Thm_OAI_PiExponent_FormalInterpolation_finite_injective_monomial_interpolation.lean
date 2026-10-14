-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_injective_monomial_interpolation
-- name    : OAI.PiExponent.FormalInterpolation.finite_injective_monomial_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T08:55:01.715359+00:00
-- url     : https://prove2.me/theorems/c74906e9-73f2-4167-ba4e-a3df855bc594
-- title:
--   Interpolate coefficients along an injective finite exponent map
-- statement:
--   For a finite index type, any injective assignment of monomial exponents and any prescribed coefficient function are realized by a multivariate polynomial supported only on the assigned exponents.

import Mathlib.Algebra.MvPolynomial.Basic

theorem OAI.PiExponent.FormalInterpolation.finite_injective_monomial_interpolation
    {alpha sigma R : Type*} [Fintype alpha] [DecidableEq sigma] [CommSemiring R]
    (e : alpha -> Finsupp sigma Nat) (he : Function.Injective e) (x : alpha -> R) :
    Exists fun P : MvPolynomial sigma R =>
      And (forall a : alpha, P.coeff (e a) = x a)
        (P.support ⊆ Finset.univ.image e) := by sorry
