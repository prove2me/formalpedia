-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative
-- name    : IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/dd05e8b0-8d92-5aec-ae1d-72ce351ebfff
-- title:
--   Hasse–Arf condition for abelian lower ramification chains
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $G$ be a finite group acting on $R$ by ring automorphisms (a `MulSemiringAction`), the action being faithful, with $G$ commutative. Assume that the maximal ideal of $R$ lies over the maximal ideal of the subring $R^{G}$ of $G$-fixed points, that the residue extension $R^{G}/\mathfrak m_{R^{G}} \to R/\mathfrak m_R$ is separable, and that the residue field of $R$ is perfect. For $i \in \mathbb N$ let $G_i = \mathrm{lowerRamificationGroup}\,R\,G\,i$ be the inertia subgroup of the ideal $\mathfrak m_R^{\,i+1}$, that is the subgroup of those $\sigma \in G$ acting trivially on $R/\mathfrak m_R^{\,i+1}$. The conclusion is that this chain satisfies [`RamificationChain.HasseArfChain`](def/RamificationChain_Wild.html#L16): for every $i$ with $G_i \neq G_{i+1}$, the cardinality of $G_0$ divides $\sum_{j=1}^{i} |G_j|$. Equivalently, the Herbrand function $\varphi(i) = (|G_1| + \cdots + |G_i|)/|G_0|$ takes integer values at the jumps of the lower numbering.
--
--   This is the Hasse–Arf theorem in the abelian case, stated for a finite commutative group acting faithfully on a discrete valuation ring rather than for an abelian extension of local fields: the jumps of the lower ramification filtration occur at arguments where the Herbrand function is integral, so that the upper numbering filtration jumps only at integers. It is used in the project to obtain the quantitative statement about upper ramification groups recorded in [`IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow`](thm.html#IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G) := by sorry
