-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units
-- name    : IsDiscreteValuationRing.exists_monoidHom_lowerRamificationGroup_zero_residueField_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/ef81d4f8-4a94-543c-b8a0-ca4175e28f62
-- title:
--   Tame inertia quotient embeds in residue field units
-- statement:
--   Let $R$ be a commutative domain that is a discrete valuation ring, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R` and residue field $k =$ `IsLocalRing.ResidueField R`, and let $G$ be a finite group acting on $R$ by ring automorphisms; $k$ is assumed perfect. For $i \in \mathbb N$, [`IsLocalRing.lowerRamificationGroup R G i`](def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) is the inertia subgroup of $\mathfrak m^{i+1}$, i.e. the subgroup of those $g \in G$ acting trivially on $R/\mathfrak m^{i+1}$; write $G_0$ and $G_1$ for the cases $i = 0$ and $i = 1$. The theorem asserts three things simultaneously. First, there exists a monoid homomorphism $\theta : G_0 \to k^{\times}$ whose kernel is exactly $G_1 \cap G_0$, regarded via `Subgroup.subgroupOf` as a subgroup of $G_0$. Second, the quotient of $G_0$ by that subgroup is cyclic. Third, for every prime number $p$ whose image in $R$ lies in $\mathfrak m$, $p$ does not divide the relative index `Subgroup.relIndex` of $G_1$ in $G_0$, that is, the index $[G_0 : G_1 \cap G_0]$. No completeness, faithfulness of the action, or separability assumption is imposed.
--
--   This is the classical description of the tame quotient of inertia: the character $s \mapsto \overline{s\pi/\pi}$ on the inertia group of a local extension has kernel the wild inertia group, so $G_0/G_1$ is cyclic of order prime to the residue characteristic. It supplies the tame input for the Hasse–Arf bookkeeping, being cited by [`IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic`](thm.html#IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic) and by [`IsDiscreteValuationRing.relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute`](thm.html#IsDiscreteValuationRing.relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_monoidHom_lowerRamificationGroup_zero_residueField_units
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)] :
    (∃ θ : ↥(IsLocalRing.lowerRamificationGroup R G 0) →* (IsLocalRing.ResidueField R)ˣ,
        θ.ker = (IsLocalRing.lowerRamificationGroup R G 1).subgroupOf
          (IsLocalRing.lowerRamificationGroup R G 0)) ∧
    IsCyclic (↥(IsLocalRing.lowerRamificationGroup R G 0) ⧸
        (IsLocalRing.lowerRamificationGroup R G 1).subgroupOf
          (IsLocalRing.lowerRamificationGroup R G 0)) ∧
    (∀ p : ℕ, p.Prime → (p : R) ∈ IsLocalRing.maximalIdeal R →
        ¬ p ∣ (IsLocalRing.lowerRamificationGroup R G 1).relIndex
          (IsLocalRing.lowerRamificationGroup R G 0)) := by sorry
