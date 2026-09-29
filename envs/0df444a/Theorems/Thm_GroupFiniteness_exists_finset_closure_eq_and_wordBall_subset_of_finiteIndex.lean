-- Prove2me | Theorems.Thm_GroupFiniteness_exists_finset_closure_eq_and_wordBall_subset_of_finiteIndex
-- name    : GroupFiniteness.exists_finset_closure_eq_and_wordBall_subset_of_finiteIndex
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T17:45:14.124564+00:00
-- url     : https://prove2.me/theorems/81f36433-fb57-41ad-99c6-83e12a2fbbe7
-- title:
--   A subgroup of finite index has a generating set on which its elements are words no longer than in the whole group
-- statement:
--   Let $H$ be a subgroup of finite index in a group $G$, and let $S$ be a finite generating
--   set of $G$. Then there is a finite subset $U$ of $H$ which generates $H$ and for which, for every
--   $n$, an element of $H$ that is a product of at most $n$ factors from $S \cup S^{-1}$ is also a
--   product of at most $n$ factors from $U \cup U^{-1}$.
--
--   The balls are those of the published growth bundle: $\mathrm{wordBall}\ S\ n$ is the set of
--   products of at most $n$ factors, each of which lies in $S$ or has its inverse in $S$. Nothing is
--   asserted about the size of $U$, and $H$ is not assumed normal. The bound is $n$ rather than a
--   multiple of $n$ because the transversal can be chosen to represent $H$ itself by $1$.
-- source:
--   The quantitative form of Schreier's lemma. Mathlib has the lemma itself, `Subgroup.closure_mul_image_eq`: the Schreier set generates the subgroup. It records nothing about word length, and the length bound is what lets a growth estimate for the subgroup be transferred to the whole group, as in Wolf's Theorem 3.11 (J. Differential Geometry 2 (1968) 421-446, p. 431).

import Definitions.Def_Chou_Growth
import Mathlib

namespace GroupFiniteness

theorem exists_finset_closure_eq_and_wordBall_subset_of_finiteIndex {G : Type*} [Group G]
    (H : Subgroup G) [H.FiniteIndex] (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    ∃ U : Finset G, (U : Set G) ⊆ (H : Set G) ∧ Subgroup.closure (U : Set G) = H ∧
      ∀ n : ℕ, ∀ h ∈ H, h ∈ Chou.wordBall (S : Set G) n →
        h ∈ Chou.wordBall (U : Set G) n := by
  sorry

end GroupFiniteness
