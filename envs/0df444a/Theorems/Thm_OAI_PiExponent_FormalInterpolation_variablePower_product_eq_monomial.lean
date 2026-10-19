-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_variablePower_product_eq_monomial
-- name    : OAI.PiExponent.FormalInterpolation.variablePower_product_eq_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:54:32.707215+00:00
-- url     : https://prove2.me/theorems/08c837ca-50a8-42e7-9331-add5595e25a0
-- title:
--   Products of variable powers are monomials
-- statement:
--   The product over a finite variable family of the indicated powers equals the monomial whose exponent at each variable is the product of the two exponent functions.

import Mathlib.RingTheory.MvPolynomial.Ideal

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.variablePower_product_eq_monomial
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (e b : σ → Nat) :
    (∏ i, ((MvPolynomial.X i : MvPolynomial σ k) ^ e i) ^ b i) =
      MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b i)) (1 : k) := by sorry
