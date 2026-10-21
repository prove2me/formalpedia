-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedDivision_remainder_of_wellFounded_relations
-- name    : OAI.PiExponent.WeightedDivision.remainder_of_wellFounded_relations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:42:53.879382+00:00
-- url     : https://prove2.me/theorems/19ebb353-ae50-40a7-adbd-8fe226998fe0
-- title:
--   Well-founded monic relations give representatives on allowed monomials
-- statement:
--   If every disallowed monomial agrees modulo an ideal with a polynomial supported on predecessors in a well-founded relation, every polynomial has a representative supported on allowed monomials. Neither additive compatibility of the relation nor closure of the allowed set is required.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem OAI.PiExponent.WeightedDivision.remainder_of_wellFounded_relations
    {ι : Type*} {R : Type*} [DecidableEq ι] [CommRing R]
    (r : (ι →₀ ℕ) → (ι →₀ ℕ) → Prop)
    (hr : WellFounded r)
    (J : Ideal (MvPolynomial ι R))
    (A : (ι →₀ ℕ) → Prop)
    (hrel : ∀ u, ¬ A u →
      ∃ G : MvPolynomial ι R, G ∈ J ∧
        ∀ v ∈ (MvPolynomial.monomial u (1 : R) - G).support, r v u)
    (P : MvPolynomial ι R) :
    ∃ Q : MvPolynomial ι R,
      P - Q ∈ J ∧ ∀ u ∈ Q.support, A u := by sorry
