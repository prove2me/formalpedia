-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic
-- name    : IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/e40c0f08-1156-5126-af4c-2b7dde7a3a9f
-- title:
--   Hasse–Arf condition for cyclic lower ramification chains
-- statement:
--   Let $R$ be a commutative domain that is a discrete valuation ring, with maximal ideal $\mathfrak m$, and let $G$ be a finite group acting on $R$ by ring automorphisms, the action being faithful. Assume $G$ is cyclic, that $\mathfrak m$ lies over the maximal ideal of the fixed subring $R^G$, that the residue field extension $R^G/\mathfrak m_{R^G} \to R/\mathfrak m$ is separable, and that the residue field of $R$ is perfect. For $i \in \mathbb N$ write $G_i$ for the $i$-th lower ramification group, defined as the inertia subgroup of $\mathfrak m^{i+1}$ in $G$, that is, the subgroup of those $\sigma \in G$ acting trivially on $R/\mathfrak m^{i+1}$. The conclusion is that the chain $i \mapsto G_i$ satisfies the Hasse–Arf condition: for every $i \in \mathbb N$ with $G_i \neq G_{i+1}$, the order of $G_0$ divides $\sum_{j=1}^{i} |G_j|$ (an empty sum, hence $0$, when $i = 0$).
--
--   This is the Hasse–Arf theorem in the cyclic case, formulated for a cyclic group acting faithfully on a discrete valuation ring rather than for a cyclic extension of local fields. It is the arithmetic core from which the statement for commutative $G$ is obtained, and it feeds the computation of the ramification filtration sums expressing the conductor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsCyclic G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G) := by sorry
