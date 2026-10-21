-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_monomial_representatives_of_wellFounded_relations
-- name    : OAI.PiExponent.WeightedDivision.monomial_representatives_of_wellFounded_relations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:55:11.348215+00:00
-- url     : https://prove2.me/theorems/0660c5d6-709a-4c38-a155-c6e0cd4eaede
-- title:
--   Well-founded reduction of a monomial with any coefficient
-- statement:
--   For each exponent u and coefficient c, the monomial with that coefficient is congruent modulo J to a polynomial supported only on exponents satisfying A.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.monomial_representatives_of_wellFounded_relations
    {ι : Type*} {R : Type*} [DecidableEq ι] [CommRing R]
    (r : (ι →₀ ℕ) → (ι →₀ ℕ) → Prop)
    (hr : WellFounded r)
    (J : Ideal (MvPolynomial ι R))
    (A : (ι →₀ ℕ) → Prop)
    (hrel : ∀ u, ¬ A u →
      ∃ G : MvPolynomial ι R, G ∈ J ∧
        ∀ v ∈ (MvPolynomial.monomial u (1 : R) - G).support, r v u)
    (u : ι →₀ ℕ) (c : R) :
    ∃ Q : MvPolynomial ι R,
      MvPolynomial.monomial u c - Q ∈ J ∧ ∀ v ∈ Q.support, A v := by sorry
