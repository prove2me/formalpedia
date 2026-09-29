-- Prove2me | Theorems.Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one
-- name    : IsLocalRing.isPGroup_lowerRamificationGroup_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/3ccf880b-48d9-52f8-a1a3-a38b32cbffba
-- title:
--   The first ramification group is a p-group
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`, and let $G$ be a finite group acting on $R$ by ring automorphisms (a `MulSemiringAction`) with the action faithful. Let $p$ be a natural number such that the image of $p$ in $R$ lies in $\mathfrak m$, and assume the separatedness condition $\bigwedge_n \mathfrak m^{\,n} = \bot$, i.e. $\bigcap_{n} \mathfrak m^{\,n} = 0$. For $i \in \mathbb N$ the group [`IsLocalRing.lowerRamificationGroup R G i`](def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) is by definition the inertia subgroup of $G$ attached to the ideal $\mathfrak m^{\,i+1}$, that is, the subgroup of those $\sigma \in G$ with $\sigma \cdot x - x \in \mathfrak m^{\,i+1}$ for every $x \in R$. The conclusion is that for $i = 1$ this subgroup, namely $\{\sigma : \sigma \cdot x \equiv x \bmod \mathfrak m^{2}\ \text{for all } x\}$, is a $p$-group in the sense of `IsPGroup`: every one of its elements $\sigma$ satisfies $\sigma^{p^{k}} = 1$ for some $k \in \mathbb N$. No primality of $p$ is assumed.
--
--   This is the classical statement that the wild inertia group $G_1$ in the lower numbering is a $p$-group, $p$ the residue characteristic (Serre, Local Fields IV §2), here in a general local-ring setting with a faithful finite group action rather than only for local fields. It feeds into the analysis of the filtration $G_0 \supseteq G_1 \supseteq \cdots$, being used for [`IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic`](thm.html#IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocalRing.isPGroup_lowerRamificationGroup_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hsep : ⨅ n, IsLocalRing.maximalIdeal R ^ n = ⊥) :
    IsPGroup p (IsLocalRing.lowerRamificationGroup R G 1) := by sorry
