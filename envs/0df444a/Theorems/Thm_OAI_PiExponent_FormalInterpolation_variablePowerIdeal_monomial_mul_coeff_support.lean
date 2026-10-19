-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_variablePowerIdeal_monomial_mul_coeff_support
-- name    : OAI.PiExponent.FormalInterpolation.variablePowerIdeal_monomial_mul_coeff_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:41:43.88883+00:00
-- url     : https://prove2.me/theorems/50b03d1a-fe1e-4cd2-bee9-748e6755e691
-- title:
--   Support bounds for a monomial multiple
-- statement:
--   A nonzero coefficient at exponent d of a polynomial multiplied by the monomial with exponent i ↦ e i * b i forces that monomial exponent to be coordinatewise at most d. This follows from the multiplication coefficient formula and also covers zero exponents.

import Mathlib.RingTheory.MvPolynomial.Ideal

theorem OAI.PiExponent.FormalInterpolation.variablePowerIdeal_monomial_mul_coeff_support
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (e : σ → Nat) (b : σ → Nat) (q : MvPolynomial σ k)
    (d : σ →₀ Nat)
    (h : (MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b i)) (1 : k) * q).coeff d ≠ 0) :
    ∀ i, e i * b i ≤ d i := by sorry
