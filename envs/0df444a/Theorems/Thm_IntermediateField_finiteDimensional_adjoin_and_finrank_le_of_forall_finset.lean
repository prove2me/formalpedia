-- Prove2me | Theorems.Thm_IntermediateField_finiteDimensional_adjoin_and_finrank_le_of_forall_finset
-- name    : IntermediateField.finiteDimensional_adjoin_and_finrank_le_of_forall_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/1e3bf3ab-e0ad-5451-a067-c1d3f5135951
-- title:
--   Uniformly bounded finite subextensions give [F(S):F]≤ n
-- statement:
--   Let $F$ and $E$ be fields with $E$ an $F$-algebra, let $S \subseteq E$ be an arbitrary subset and let $n$ be a natural number. Assume that for every finite subset $s$ of $E$ whose underlying set is contained in $S$, the intermediate field $F(s) =$ `IntermediateField.adjoin F (↑s : Set E)` generated over $F$ by the elements of $s$ is finite-dimensional as an $F$-module and its $F$-dimension `Module.finrank` is at most $n$. The conclusion is the conjunction of the same two assertions for the possibly infinite set $S$: the intermediate field $F(S) =$ `IntermediateField.adjoin F S` is finite-dimensional over $F$ and $\operatorname{finrank}_F F(S) \le n$. Finite-dimensionality is asserted separately from the rank bound because in Mathlib the `finrank` of a module that is not finite-dimensional is $0$, so the inequality alone would carry no information; correspondingly the hypothesis must be imposed on all finite subsets of $S$, a bound on singletons being insufficient.
--
--   A standard point of elementary field theory: a bound on the degrees of all finitely generated subextensions of $F(S)$ propagates to $F(S)$ itself. It is used in the construction of a finite-dimensional intermediate field containing the images of a prescribed finite family of elements in [`ValuationSubring.exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime`](thm.html#ValuationSubring.exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_finiteDimensional_adjoin_and_finrank_le_of_forall_finset.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.finiteDimensional_adjoin_and_finrank_le_of_forall_finset
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E) (n : ℕ)
    (hS : ∀ s : Finset E, (↑s : Set E) ⊆ S →
      FiniteDimensional F ↥(IntermediateField.adjoin F (↑s : Set E)) ∧
        Module.finrank F ↥(IntermediateField.adjoin F (↑s : Set E)) ≤ n) :
    FiniteDimensional F ↥(IntermediateField.adjoin F S) ∧ Module.finrank F ↥(IntermediateField.adjoin F S) ≤ n := by sorry
