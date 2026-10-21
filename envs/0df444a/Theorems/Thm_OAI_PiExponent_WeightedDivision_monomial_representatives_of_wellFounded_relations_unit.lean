-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_monomial_representatives_of_wellFounded_relations_unit
-- name    : OAI.PiExponent.WeightedDivision.monomial_representatives_of_wellFounded_relations_unit
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:03:19.190265+00:00
-- url     : https://prove2.me/theorems/235e2114-f5c2-4f6e-b095-9b218ed339ba
-- title:
--   Well-founded reduction of a unit monomial
-- statement:
--   For every exponent u, the unit-coefficient monomial is congruent modulo J to a polynomial supported only on exponents satisfying A.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.monomial_representatives_of_wellFounded_relations_unit
    {ι : Type*} {R : Type*} [DecidableEq ι] [CommRing R]
    (r : (ι →₀ ℕ) → (ι →₀ ℕ) → Prop)
    (hr : WellFounded r)
    (J : Ideal (MvPolynomial ι R))
    (A : (ι →₀ ℕ) → Prop)
    (hrel : ∀ u, ¬ A u →
      ∃ G : MvPolynomial ι R, G ∈ J ∧
        ∀ v ∈ (MvPolynomial.monomial u (1 : R) - G).support, r v u)
    (u : ι →₀ ℕ) :
    ∃ Q : MvPolynomial ι R,
      MvPolynomial.monomial u (1 : R) - Q ∈ J ∧ ∀ v ∈ Q.support, A v := by sorry
