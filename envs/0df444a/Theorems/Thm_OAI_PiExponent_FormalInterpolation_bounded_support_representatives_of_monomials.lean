-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_support_representatives_of_monomials
-- name    : OAI.PiExponent.FormalInterpolation.bounded_support_representatives_of_monomials
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:21:13.610115+00:00
-- url     : https://prove2.me/theorems/9415843d-1ce0-4e38-a0d7-2063d4950867
-- title:
--   Bounded representatives for monomials extend to all polynomials
-- statement:
--   For a fixed bound, if every monomial has a representative modulo the ideal supported inside the coordinatewise exponent box, then every multivariate polynomial has such a representative.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_support_representatives_of_monomials
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (hmono : ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J) :
    ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧ P - R ∈ J := by sorry
