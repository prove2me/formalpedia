-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
-- name    : IsDiscreteValuationRing.exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/1b9ae935-0db9-54b5-91bb-bdb78e2b24e6
-- title:
--   Trace surjectivity for a single lower ramification jump
-- statement:
--   Let $B$ be a discrete valuation ring which is a commutative domain, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal B`, and let $G$ be a finite group acting on $B$ by ring automorphisms, the action being faithful; write $A =$ `FixedPoints.subring B G` for the subring of $G$-invariants. Assume $\mathfrak m$ lies over the maximal ideal $\mathfrak m_A$ of $A$, and that the residue extension $A/\mathfrak m_A \to B/\mathfrak m$ is separable. Let $t$ be a natural number such that the $t$-th lower ramification group is all of $G$ and the $(t+1)$-st is trivial; here the $i$-th lower ramification group is the inertia subgroup of $\mathfrak m^{i+1}$, i.e. the subgroup of those $\sigma \in G$ acting trivially on $B/\mathfrak m^{i+1}$. Thus every element of $G$ acts trivially modulo $\mathfrak m^{t+1}$, and only the identity acts trivially modulo $\mathfrak m^{t+2}$. Then for every natural number $m$ and every $G$-invariant $c \in B$ lying in $\mathfrak m^{n}$ with $n = |G| \cdot \lfloor (m + (t+1)(|G|-1))/|G| \rfloor$ (natural-number subtraction and division, $|G| =$ `Nat.card G`), there exists $y \in \mathfrak m^{m}$ whose trace $\sum_{\sigma \in G} \sigma \cdot y$ equals $c$.
--
--   This is the surjectivity half of Serre's computation of the trace of the powers of the maximal ideal in a totally ramified layer, $\mathrm{Tr}(\mathfrak m^{m}) = \mathfrak m_A^{\lfloor (m+d)/e\rfloor}$ with $d = (t+1)(|G|-1)$, specialised to the case of a single lower ramification jump at $t$. It is used in the proof of [`IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card`](thm.html#IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card), in the analysis of the norm and trace maps on the unit filtration above such a layer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (m : ℕ) (c : B) (hcG : ∀ σ : G, σ • c = c)
    (hc : c ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * ((m + (t + 1) * (Nat.card G - 1)) / Nat.card G))) :
    ∃ y : B, y ∈ IsLocalRing.maximalIdeal B ^ m ∧ ∑ᶠ σ : G, σ • y = c := by sorry
