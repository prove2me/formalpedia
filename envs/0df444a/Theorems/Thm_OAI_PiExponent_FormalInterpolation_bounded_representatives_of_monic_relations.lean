-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_of_monic_relations
-- name    : OAI.PiExponent.FormalInterpolation.bounded_representatives_of_monic_relations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:20:43.011747+00:00
-- url     : https://prove2.me/theorems/66554b61-6b15-4b51-98b8-0aa925b03cb7
-- title:
--   Monic variable relations give bounded-support representatives
-- statement:
--   If each variable class in a polynomial quotient is annihilated by a monic polynomial over Complex, every monomial has a representative modulo the ideal whose support exponents are bounded coordinatewise by one uniform strict bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_representatives_of_monic_relations
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hrel : ∀ i : Fin (m + 1),
      ∃ p : Polynomial Complex,
        p.Monic ∧ Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X i)) p = 0) :
    ∃ N : Nat, ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by sorry
