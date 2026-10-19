-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_support_gives_weighted_polynomial
-- name    : OAI.PiExponent.FormalInterpolation.bounded_support_gives_weighted_polynomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:15:36.775082+00:00
-- url     : https://prove2.me/theorems/9aac7d8f-f56c-4b61-b044-85998358fc69
-- title:
--   A finite coordinate box has bounded weighted degree
-- statement:
--   For positive coordinate weights, every polynomial whose support exponents lie in a fixed finite coordinate box belongs to a weighted-polynomial subtype with a uniform weighted-degree bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_support_gives_weighted_polynomial
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (N : Nat) :
    ∃ C : Real, ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      (∀ a ∈ P.support, ∀ i : Fin (m + 1), a i < N) →
      ∃ Q : WeightedPolynomial w0 w C, Q.val = P := by sorry
