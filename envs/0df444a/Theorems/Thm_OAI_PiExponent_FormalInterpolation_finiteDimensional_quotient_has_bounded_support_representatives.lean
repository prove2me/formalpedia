-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteDimensional_quotient_has_bounded_support_representatives
-- name    : OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_has_bounded_support_representatives
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:15:20.740997+00:00
-- url     : https://prove2.me/theorems/6053384b-5732-48b1-afaf-4876d75d3642
-- title:
--   Finite-dimensional quotients have bounded-support representatives
-- statement:
--   If the quotient of a multivariate complex polynomial ring by an ideal is finite-dimensional, there is a uniform coordinatewise exponent bound such that every polynomial has a representative modulo the ideal supported inside that finite exponent box.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_has_bounded_support_representatives
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ J)) :
    ∃ N : Nat, ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ a ∈ R.support, ∀ i : Fin (m + 1), a i < N) ∧ P - R ∈ J := by sorry
