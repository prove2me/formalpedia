-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_translated_polynomial_full_jets_interpolate
-- name    : OAI.PiExponent.FormalInterpolation.finite_translated_polynomial_full_jets_interpolate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:40:20.952273+00:00
-- url     : https://prove2.me/theorems/b4ae670f-709b-4665-8d77-1253c6fa8d68
-- title:
--   Finite full Taylor jets interpolate at distinct points
-- statement:
--   For finitely many distinct complex points, one multivariate polynomial can realize arbitrary prescribed translated coefficients at every exponent whose total degree is at most a fixed bound.

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic

theorem OAI.PiExponent.FormalInterpolation.finite_translated_polynomial_full_jets_interpolate
    {n : Nat} {J : Type} [Fintype J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (z : J → (Fin n →₀ Nat) → Complex) :
    ∃ Q : MvPolynomial (Fin n) Complex,
      ∀ (j : J) (α : Fin n →₀ Nat),
        (∑ i : Fin n, α i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c j i) + MvPolynomial.X i) Q).coeff α
          = z j α := by sorry
