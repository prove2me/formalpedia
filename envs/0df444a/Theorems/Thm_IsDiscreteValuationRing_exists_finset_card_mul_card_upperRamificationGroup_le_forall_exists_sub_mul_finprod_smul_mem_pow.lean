-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow
-- name    : IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/abec7794-9155-58f9-b195-2ffad240d273
-- title:
--   Graded norm cokernel bound via upper ramification groups
-- statement:
--   Let $B$ be a discrete valuation ring (a commutative domain) with maximal ideal $\mathfrak m$, and let $G$ be a finite abelian group acting faithfully on $B$ by ring automorphisms, such that $\mathfrak m$ lies over the maximal ideal of the fixed subring $B^G$, the residue extension of $B^G \subseteq B$ is separable, and the residue ring $B/\mathfrak m$ is finite. Here $G_i$ denotes the $i$-th lower ramification group, namely the inertia subgroup of $G$ acting on $\mathfrak m^{i+1}$, and for $v \in \mathbb Q$ the upper ramification group $G^{v}$ is $G_{k(v)}$ with $k(v) = \inf\{n \in \mathbb N : v \le \varphi(n)\}$, $\varphi$ being the Herbrand function $\varphi(u) = u$ for $u \le 0$ and $\varphi(u) = \bigl(\sum_{i=1}^{\lfloor u \rfloor} |G_i| + (u - \lfloor u \rfloor)\,|G_{\lfloor u \rfloor + 1}|\bigr)/|G_0|$ otherwise. Then for every $m \in \mathbb N$ there is a finite set $S \subseteq B$ such that $|S| \cdot |G^{m+1}| \le |G^{m}|$, every element of $S$ is a unit fixed by $G$, and every $G$-fixed unit $a$ with $a - 1 \in \mathfrak m^{|G_0| \, m}$ can be written, for some $s \in S$ and some unit $b$ with $b - 1 \in \mathfrak m^{k(m)}$, so that $a - s \prod_{\sigma \in G} \sigma \cdot b \in \mathfrak m^{|G_0|\,(m+1)}$.
--
--   This is the graded form of Serre's computation of the norm map on the unit filtration: the cokernel of the norm from the $k(m)$-th graded piece of the units of $B$ to the $m$-th graded piece of the units of $B^G$ has order at most $[G^{m}:G^{m+1}]$. It feeds the local computation of the Artin map on upper ramification groups, in [`M4aHerbrand.exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup`](thm.html#M4aHerbrand.exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B] [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)] (m : ℕ) :
    ∃ S : Finset B,
      S.card * Nat.card (IsLocalRing.upperRamificationGroup B G ((m + 1 : ℕ) : ℚ)) ≤
          Nat.card (IsLocalRing.upperRamificationGroup B G (m : ℚ)) ∧
      (∀ s ∈ S, IsUnit s ∧ ∀ σ : G, σ • s = s) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) →
        a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card (IsLocalRing.lowerRamificationGroup B G 0) * m) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧
          b - 1 ∈ IsLocalRing.maximalIdeal B ^ IsLocalRing.upperRamificationIndex B G m ∧
          a - s * ∏ᶠ σ : G, σ • b ∈
            IsLocalRing.maximalIdeal B ^ (Nat.card (IsLocalRing.lowerRamificationGroup B G 0) * (m + 1)) := by sorry
