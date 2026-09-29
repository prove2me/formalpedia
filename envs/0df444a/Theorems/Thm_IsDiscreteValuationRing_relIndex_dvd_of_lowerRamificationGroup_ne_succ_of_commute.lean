-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute
-- name    : IsDiscreteValuationRing.relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/d44277ae-26ce-54f5-8de8-5fb7f66969b1
-- title:
--   Lower jumps are divisible by [G₀:G₁] when G₀ is abelian
-- statement:
--   Let $R$ be a commutative domain that is a discrete valuation ring, and let $G$ be a finite group acting on $R$ by ring automorphisms, the residue field $R/\mathfrak m$ being assumed perfect. For $j \in \mathbb{N}$ write $G_j$ for the $j$-th lower ramification group, defined as the inertia subgroup of $G$ attached to the ideal $\mathfrak m^{j+1}$, i.e. the subgroup of those $s \in G$ acting trivially on $R/\mathfrak m^{j+1}$. Assume that any two elements of $G_0$ commute, and let $i \ge 1$ be a natural number at which a jump occurs, in the sense that $G_i \ne G_{i+1}$ as subgroups of $G$. Then the relative index of $G_1$ in $G_0$, namely the index of $G_0 \cap G_1$ in $G_0$ (so $[G_0 : G_1]$, since $G_1 \le G_0$), divides $i$.
--
--   This is the congruence on the wild jumps of an abelian inertia group, classically Serre's Corps locaux IV, §2, Proposition 9 and its corollary: for $G_0$ commutative every jump $i \ge 1$ of the lower filtration is a multiple of the tame index $e_0 = [G_0:G_1]$. It is used in the construction of the Hasse–Arf chain of lower ramification groups in the cyclic case, via the homomorphism $G_0 \to (R/\mathfrak m)^\times$ with kernel $G_1$ supplied by [`IsDiscreteValuationRing.exists_monoidHom_lowerRamificationGroup_zero_residueField_units`](thm.html#IsDiscreteValuationRing.exists_monoidHom_lowerRamificationGroup_zero_residueField_units).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hcomm : ∀ s ∈ IsLocalRing.lowerRamificationGroup R G 0,
      ∀ t ∈ IsLocalRing.lowerRamificationGroup R G 0, Commute s t)
    {i : ℕ} (hi : 1 ≤ i)
    (hjump : IsLocalRing.lowerRamificationGroup R G i ≠ IsLocalRing.lowerRamificationGroup R G (i + 1)) :
    (IsLocalRing.lowerRamificationGroup R G 1).relIndex (IsLocalRing.lowerRamificationGroup R G 0) ∣ i := by sorry
