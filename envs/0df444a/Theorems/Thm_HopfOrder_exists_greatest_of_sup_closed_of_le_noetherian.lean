-- Prove2me | Theorems.Thm_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian
-- name    : HopfOrder.exists_greatest_of_sup_closed_of_le_noetherian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/fba2bf01-fe97-5f9f-9ecb-171cb88855d7
-- title:
--   A sup-closed bounded family of subalgebras has a greatest member
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative $R$-algebra, and let $P$ be an arbitrary predicate on the $R$-subalgebras of $A$. Assume: (i) $P$ is closed under binary joins, i.e. $P(S \sqcup S')$ holds whenever $P(S)$ and $P(S')$ hold, where $\sqcup$ is the join in the lattice of $R$-subalgebras of $A$; (ii) there is an $R$-subalgebra $M \subseteq A$ which is Noetherian as an $R$-module (the instance `IsNoetherian R M`) and which bounds the family, in the sense that $S \le M$ for every $S$ with $P(S)$; (iii) the family is nonempty, i.e. some $R$-subalgebra $S$ satisfies $P(S)$. The conclusion is that there exists an $R$-subalgebra $S$ of $A$ with $P(S)$ such that $S' \le S$ for every $S'$ satisfying $P(S')$ — that is, the family has a greatest element, stated in unbundled form as the conjunction of membership and the universal upper-bound property rather than via `IsGreatest`.
--
--   This is the order-theoretic step behind the existence of a maximal prolongation: a family of subalgebras that is stable under joins, nonempty, and contained in a subalgebra Noetherian over the base has a greatest member. It is used by [`HopfOrder.exists_isGreatest`](thm.html#HopfOrder.exists_isGreatest) to produce the largest Hopf order inside a given Hopf algebra, the family being bounded by an integral closure that is finite over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u w

theorem HopfOrder.exists_greatest_of_sup_closed_of_le_noetherian
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (P : Subalgebra R A → Prop) (hsup : ∀ S S', P S → P S' → P (S ⊔ S'))
    (M : Subalgebra R A) [IsNoetherian R M] (hle : ∀ S, P S → S ≤ M) (h0 : ∃ S, P S) :
    ∃ S, P S ∧ ∀ S', P S' → S' ≤ S := by sorry
