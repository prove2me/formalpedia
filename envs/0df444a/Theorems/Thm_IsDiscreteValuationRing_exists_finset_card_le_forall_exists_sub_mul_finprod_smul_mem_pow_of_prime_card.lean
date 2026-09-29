-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
-- name    : IsDiscreteValuationRing.exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/d4f85ddb-0483-5f01-b865-63b86e529218
-- title:
--   Graded norm cokernels in a ramified layer of prime degree
-- statement:
--   Let $B$ be a commutative domain which is a discrete valuation ring, with maximal ideal $\mathfrak m_B$, and let $G$ be a finite group acting faithfully on $B$ by ring automorphisms, with $A := B^{G}$ the subring of fixed points; assume $\mathfrak m_B$ lies over $\mathfrak m_A$, that the residue extension $B/\mathfrak m_B$ over $A/\mathfrak m_A$ is separable, and that $B/\mathfrak m_B$ is finite. Suppose $\ell := |G|$ is prime, and let $t \in \mathbb N$ be such that the inertia subgroup of $\mathfrak m_B^{t+1}$ in $G$ is all of $G$ while the inertia subgroup of $\mathfrak m_B^{t+2}$ is trivial. Then for every $y \in \mathbb N$ there is a finite subset $S \subseteq B$ of cardinality at most $\ell$ if $y = t$ and at most $1$ otherwise, each element $s \in S$ being a unit fixed by every $\sigma \in G$ with $s - 1 \in \mathfrak m_B^{\ell y}$, such that every unit $a \in B$ fixed by every $\sigma \in G$ with $a - 1 \in \mathfrak m_B^{\ell y}$ can be written, for some $s \in S$ and some unit $b \in B$ with $b - 1 \in \mathfrak m_B^{\psi(y)}$, where $\psi(y) = y$ for $y \le t$ and $\psi(y) = t + \ell\,(y - t)$ otherwise, so that $a - s \prod_{\sigma \in G} \sigma \cdot b \in \mathfrak m_B^{\ell (y+1)}$ (the product being taken as a finite product over $G$).
--
--   This is the quantitative form of Serre's computation of the graded pieces of the norm map in a ramified layer of prime degree with a single ramification jump at $t$ (Corps locaux V §3, Prop. 5): the cokernel of the induced map on the unit filtration has order at most $\ell$ at the jump and is trivial elsewhere, the set $S$ providing explicit coset representatives. It is used by [`IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow`](thm.html#IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow), where such representatives are assembled over the whole unit filtration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (y : ℕ) :
    ∃ S : Finset B, S.card ≤ (if y = t then Nat.card G else 1) ∧
      (∀ s ∈ S, IsUnit s ∧ (∀ σ : G, σ • s = s) ∧ s - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y)) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) → a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧
          b - 1 ∈ IsLocalRing.maximalIdeal B ^ (if y ≤ t then y else t + Nat.card G * (y - t)) ∧
          a - s * ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (y + 1)) := by sorry
