-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_has_bounded_support_representatives
-- name    : OAI.PiExponent.FormalInterpolation.monomial_has_bounded_support_representatives
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:20:57.689775+00:00
-- url     : https://prove2.me/theorems/8c3ef096-d5a9-4cbe-840f-72678e6876e8
-- title:
--   Monomials have bounded-support representatives in finite-dimensional quotients
-- statement:
--   If the polynomial quotient is finite-dimensional over Complex, there is one coordinatewise exponent bound such that every monomial has a representative modulo the ideal supported strictly below that bound in every coordinate.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.monomial_has_bounded_support_representatives
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ J)) :
    ∃ N : Nat, ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by sorry
