-- Prove2me | Theorems.Thm_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex
-- name    : M4aLocalCFT.herbrandQuotient_eq_one_of_cohTrivial_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/7cfaff43-56dc-5094-bbd8-19de9ab0720f
-- title:
--   Herbrand quotient is 1 modulo a trivial finite-index subgroup
-- statement:
--   Let $M$ be a commutative group, written multiplicatively, and let $D, N \colon M \to M$ be group endomorphisms such that $D(N x) = 1$ and $N(D x) = 1$ for all $x \in M$. Let $V \le M$ be a subgroup of finite index which is stable under both maps, in the sense that $D v \in V$ and $N v \in V$ for every $v \in V$, and suppose that $V$ is cohomologically trivial elementwise: every $v \in V$ with $D v = 1$ is of the form $N w$ with $w \in V$, and every $v \in V$ with $N v = 1$ is of the form $D w$ with $w \in V$. The conclusion is twofold: the cardinality (as `Nat.card`) of the quotient of $\ker D$ by the subgroup $\operatorname{im} N \cap \ker D$ (formed as the preimage of $N.\mathrm{range}$ in $\ker D$) equals the cardinality of the quotient of $\ker N$ by $\operatorname{im} D \cap \ker N$; and this common cardinality is nonzero, i.e. both of these Tate-type quotient groups are finite of the same order.
--
--   This is the element-level multiplicative form of the two standard facts about Herbrand quotients for a cyclic group action — that the quotient of a finite module is $1$, and that passing to $M/V$ along a cohomologically trivial stable subgroup $V$ does not change the two Tate groups — with $D(x) = g(x)/x$ and $N$ the norm for a generator $g$ of a finite cyclic group. It is used in the computation of the Herbrand quotient of the unit group of a local field, via [`M4aLocalCFT.unitsDecomp_herbrandQuotient_eq_one`](thm.html#M4aLocalCFT.unitsDecomp_herbrandQuotient_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex.lean

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem M4aLocalCFT.herbrandQuotient_eq_one_of_cohTrivial_finiteIndex
    {M : Type*} [CommGroup M] (D N : M →* M)
    (hDN : ∀ x, D (N x) = 1) (hND : ∀ x, N (D x) = 1)
    (V : Subgroup M) [V.FiniteIndex]
    (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V)
    (h0 : ∀ v ∈ V, D v = 1 → ∃ w ∈ V, N w = v)
    (h1 : ∀ v ∈ V, N v = 1 → ∃ w ∈ V, D w = v) :
    Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) =
      Nat.card (N.ker ⧸ (D.range.subgroupOf N.ker)) ∧
    Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) ≠ 0 := by sorry
