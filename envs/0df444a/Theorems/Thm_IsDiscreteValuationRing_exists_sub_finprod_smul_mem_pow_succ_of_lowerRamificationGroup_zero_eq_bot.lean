-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot
-- name    : IsDiscreteValuationRing.exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/5c422a1f-8964-5d74-a5b0-a9afda5f456e
-- title:
--   Norms are surjective on graded unit pieces when G₀=1
-- statement:
--   Let $B$ be a discrete valuation ring which is a domain, let $G$ be a finite group acting on $B$ by ring automorphisms, and assume the action is faithful. Write $A =$ `FixedPoints.subring B G` for the subring of $G$-invariants. Assume that the maximal ideal of $B$ lies over the maximal ideal of $A$, that the residue extension $B/\mathfrak m_B$ over $A/\mathfrak m_A$ is separable, and that the residue field $B/\mathfrak m_B$ is finite. Assume further that the zeroth lower ramification group vanishes, i.e. the inertia subgroup of $\mathfrak m_B^{0+1} = \mathfrak m_B$ in $G$ — the subgroup of those $\sigma \in G$ with $\sigma x - x \in \mathfrak m_B$ for all $x \in B$ — is trivial. Then for every natural number $m$ and every unit $a$ of $B$ which is fixed by every $\sigma \in G$ and satisfies $a - 1 \in \mathfrak m_B^m$, there exists a unit $b$ of $B$ with $b - 1 \in \mathfrak m_B^m$ and $$a - \prod_{\sigma \in G}^{\mathrm f} \sigma \cdot b \in \mathfrak m_B^{m+1},$$ the product being the finite product (`finprod`) over $G$ of the translates of $b$, i.e. the norm of $b$.
--
--   This is the graded form of the classical statement that in an unramified extension of local fields the norm map is surjective on units: the norm is onto on each quotient $U^{(m)}/U^{(m+1)}$ of the filtration of principal units. It feeds into [`IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow`](thm.html#IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow), where successive approximations of this kind are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_sub_finprod_smul_mem_pow_succ_of_lowerRamificationGroup_zero_eq_bot
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)]
    (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊥) (m : ℕ)
    (a : B) (ha : IsUnit a) (hfix : ∀ σ : G, σ • a = a) (ham : a - 1 ∈ IsLocalRing.maximalIdeal B ^ m) :
    ∃ b : B, IsUnit b ∧ b - 1 ∈ IsLocalRing.maximalIdeal B ^ m ∧
      a - ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (m + 1) := by sorry
