-- Prove2me | Theorems.Thm_Ideal_forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem
-- name    : Ideal.forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/00a1978b-a44b-507a-857f-85f14e8c039f
-- title:
--   Trivial residue extension from trivial action of the stabiliser
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and let $G$ be a finite group acting on $B$ by ring and semiring automorphisms, the action commuting with the $A$-action on $B$, and such that $A \to B$ is invariant in the sense of `Algebra.IsInvariant A B G`. Let $P$ be a maximal ideal of $A$ and $Q$ a maximal ideal of $B$ lying over $P$, and suppose the residue ring $B/Q$ is finite. Assume further that every $g \in G$ stabilising $Q$ (i.e. $g \bullet Q = Q$) acts trivially on the residue field, meaning $g \bullet b - b \in Q$ for all $b \in B$. The conclusion is that the residue extension is trivial in the strong form: for every $b \in B$ there is $a \in A$ with $b - \mathrm{algebraMap}_{A,B}(a) \in Q$, that is, the induced map $A/P \to B/Q$ is surjective.
--
--   This is the standard statement that if inertia at $Q$ fills up the decomposition group, i.e. the stabiliser of $Q$ acts trivially on $B/Q$, then the residue field does not grow. It is used in the study of the model of $X_1(p)$, in [`ModularCurve.XOneP.forall_exists_sub_mem_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul`](thm.html#ModularCurve.XOneP.forall_exists_sub_mem_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul), where it supplies the triviality of residue extensions at certain closed points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (P : Ideal A) [P.IsMaximal] (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver P] [Finite (B ⧸ Q)]
    (htriv : ∀ g : G, g • Q = Q → ∀ b : B, g • b - b ∈ Q) :
    ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ Q := by sorry
