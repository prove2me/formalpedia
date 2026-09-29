-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_differentEqPowFiltrationSum_fixedPoints_subring
-- name    : IsDiscreteValuationRing.differentEqPowFiltrationSum_fixedPoints_subring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/f0e5307c-59e9-5a2f-8bb5-bc2d399f4db5
-- title:
--   Hilbert's different formula for a faithful finite action on a DVR
-- statement:
--   Let $B$ be a commutative domain which is a discrete valuation ring, and let $G$ be a finite group acting on $B$ by ring automorphisms (a `MulSemiringAction`), the action being faithful. Write $A =$ `FixedPoints.subring B G` for the subring of $G$-invariants. Assume the maximal ideal $\mathfrak m_B$ of $B$ lies over the maximal ideal $\mathfrak m_A$ of $A$, and that the residue extension $A/\mathfrak m_A \to B/\mathfrak m_B$ is separable. For $i \in \mathbb N$ the $i$-th lower ramification group is $G_i = (\mathfrak m_B^{\,i+1}).\mathrm{inertia}\,G$, the subgroup of those $g \in G$ whose action is trivial modulo $\mathfrak m_B^{\,i+1}$. The conclusion is the predicate [`DifferentEqPowFiltrationSum A B G`](def/DifferentFiltrationFormula.html#L76): for every natural number $N$ such that $G_N$ is the trivial subgroup, the different ideal of $B$ over $A$ satisfies
--   $$\mathfrak d_{B/A} = \mathfrak m_B^{\;\sum_{i < N} (\#G_i - 1)},$$
--   the exponent being the sum over $i \in \{0,\dots,N-1\}$ of $\#G_i - 1$ computed with truncated subtraction of natural numbers.
--
--   This is Hilbert's formula for the valuation of the different in terms of the lower ramification filtration, here in the abstract setting of a discrete valuation ring carrying a faithful finite action with separable residue extension rather than for an extension of local fields. It feeds the computation of the discriminant of a fixed field in [`NumberField.card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0`](thm.html#NumberField.card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_differentEqPowFiltrationSum_fixedPoints_subring.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_DifferentFiltrationFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.differentEqPowFiltrationSum_fixedPoints_subring
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)] :
    DifferentEqPowFiltrationSum (FixedPoints.subring B G) B G := by sorry
