-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient
-- name    : IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/e5313d50-1a83-5671-a460-95e8f9ce8f3c
-- title:
--   Hasse–Arf for abelian G from its cyclic quotients
-- statement:
--   Let $R$ be a discrete valuation ring (a local domain with the usual typeclass assumptions) and let $G$ be a finite group acting on $R$ by ring automorphisms, the action being faithful and the group commutative. Assume further that the maximal ideal of $R$ lies over the maximal ideal of the fixed subring $R^{G} =$ `FixedPoints.subring R G`, that the residue extension $R^{G}/\mathfrak m_{R^{G}} \to R/\mathfrak m_R$ is separable, and that the residue field of $R$ is perfect. For a ring $S$ with a group $\Gamma$ acting on it, write $\Gamma_i$ for the $i$-th lower ramification group, defined as the inertia subgroup of $\mathfrak m_S^{\,i+1}$ in $\Gamma$, and say that a chain $i \mapsto \Gamma_i$ of subgroups satisfies the Hasse–Arf condition when for every $i$ with $\Gamma_i \neq \Gamma_{i+1}$ the cardinality of $\Gamma_0$ divides $\sum_{j=1}^{i} |\Gamma_j|$. The hypothesis is that for every normal subgroup $H \le G$ with $G/H$ cyclic, the lower ramification chain of $G/H$ acting on the fixed subring $R^{H}$ satisfies the Hasse–Arf condition. The conclusion is that the lower ramification chain of $G$ acting on $R$ satisfies the Hasse–Arf condition.
--
--   This is the first reduction in the proof of the Hasse–Arf theorem for an abelian group: the divisibility statement for $G$ itself follows from the corresponding statements for the cyclic quotients $G/H$ acting on the fixed subrings $R^{H}$, via Herbrand's theorem relating the lower numbering for $G$ to the upper numbering for $G/H$. It is the step invoked by [`IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative`](thm.html#IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative), which supplies the cyclic case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hcyc : ∀ (H : Subgroup G) [H.Normal], IsCyclic (G ⧸ H) →
      RamificationChain.HasseArfChain
        (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H))) :
    RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G) := by sorry
