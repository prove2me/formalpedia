-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_span_of_bounded_weight_representatives
-- name    : OAI.PiExponent.FormalInterpolation.ideal_span_of_bounded_weight_representatives
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:26:48.411423+00:00
-- url     : https://prove2.me/theorems/d6f765ee-c6c1-499d-9db2-94c08d3761b7
-- title:
--   Bounded quotient representatives give bounded ideal generators
-- statement:
--   With positive real variable weights and D ≥ 0, bounded representatives of every polynomial quotient class imply that the ideal is generated in weight at most D plus the sum of variable weights. Choose a quotient basis from bounded monomials and use its multiplication-table relations together with the unit relation. The statement includes the whole-ring ideal and one-variable case.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.ideal_span_of_bounded_weight_representatives
    (m : Nat) (w : Fin (m + 1) → Real) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (D : Real) (hD : 0 ≤ D)
    (hrep : ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
        P - Q ∈ I ∧
        ∀ a ∈ Q.support, ∑ i, w i * (a i : Real) ≤ D) :
    Ideal.span {P : MvPolynomial (Fin (m + 1)) Complex |
      P ∈ I ∧
      ∀ a ∈ P.support, ∑ i, w i * (a i : Real) ≤ D + ∑ i, w i} = I := by sorry
