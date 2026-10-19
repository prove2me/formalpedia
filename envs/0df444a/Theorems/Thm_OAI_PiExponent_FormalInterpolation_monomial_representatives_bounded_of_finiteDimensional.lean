-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_representatives_bounded_of_finiteDimensional
-- name    : OAI.PiExponent.FormalInterpolation.monomial_representatives_bounded_of_finiteDimensional
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:26:35.574933+00:00
-- url     : https://prove2.me/theorems/7c93d258-8681-41e2-a3fb-cb386c8ebb21
-- title:
--   Finite-dimensional polynomial quotients admit bounded monomial representatives
-- statement:
--   If a quotient of a polynomial ring in finitely many variables over Complex is finite-dimensional, then every monomial has a representative modulo the ideal supported in one fixed coordinatewise bounded exponent box.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.monomial_representatives_bounded_of_finiteDimensional
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfd : FiniteDimensional Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J)) :
    ∃ N : Nat, ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by sorry
