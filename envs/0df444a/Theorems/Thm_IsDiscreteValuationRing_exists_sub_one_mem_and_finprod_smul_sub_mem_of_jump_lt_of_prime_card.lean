-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
-- name    : IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/a23ddb61-2473-558d-b798-7d3e21cda184
-- title:
--   Norm surjectivity above the ramification jump
-- statement:
--   Let $B$ be a commutative domain which is a discrete valuation ring, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal B`, and let $G$ be a finite group acting faithfully on $B$ by ring automorphisms; write $A =$ `FixedPoints.subring B G` for the subring of $G$-invariants. Assume $\mathfrak m$ lies over the maximal ideal of $A$ and that the residue extension $A/\mathfrak m_A \to B/\mathfrak m$ is separable. Put $\ell =$ `Nat.card G` and assume $\ell$ is prime. Let $t \in \mathbb N$ be such that the $t$-th lower ramification group, defined as the inertia subgroup of $\mathfrak m^{t+1}$ in $G$ (the $\sigma$ acting trivially on $\mathfrak m^{t+1}$ in the sense of `Ideal.inertia`), is all of $G$, while the $(t+1)$-st one, the inertia subgroup of $\mathfrak m^{t+2}$, is trivial. Let $n > t$ and let $a \in A$ satisfy $a - 1 \in \mathfrak m^{\ell n}$. Then there exists $b \in B$ with $b - 1 \in \mathfrak m^{t + \ell(n-t)}$ and $\bigl(\prod_{\sigma \in G} \sigma \cdot b\bigr) - a \in \mathfrak m^{\ell(n+1)}$, the product being the finite product over all of $G$.
--
--   This is the surjectivity half of the classical description of the norm on the filtration of units of a ramified extension of prime degree, as in Serre's Corps locaux V §3: above the ramification jump the induced map $U_B^{(\psi(n))}/U_B^{(\psi(n)+1)} \to U_A^{(n)}/U_A^{(n+1)}$ is onto, with $\psi(n) = t + \ell(n-t)$. It feeds the construction of a bounded set of norm representatives for the unit filtration in [`IsDiscreteValuationRing.exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card`](thm.html#IsDiscreteValuationRing.exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime)
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (n : ℕ) (hn : t < n) (a : FixedPoints.subring B G)
    (ha : (a : B) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * n)) :
    ∃ b : B, b - 1 ∈ IsLocalRing.maximalIdeal B ^ (t + Nat.card G * (n - t)) ∧
      (∏ᶠ σ : G, σ • b) - a ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (n + 1)) := by sorry
