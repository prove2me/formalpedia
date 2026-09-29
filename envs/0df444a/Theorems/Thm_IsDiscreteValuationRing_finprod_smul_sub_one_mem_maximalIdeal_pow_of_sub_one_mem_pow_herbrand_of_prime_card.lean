-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card
-- name    : IsDiscreteValuationRing.finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/ba4b1fdb-8984-50e5-829a-ae0a6162c581
-- title:
--   Norms of higher units via the Herbrand function, prime degree
-- statement:
--   Let $B$ be a discrete valuation ring which is a domain, with maximal ideal $\mathfrak m$, and let $G$ be a finite group acting faithfully on $B$ by ring automorphisms; assume $\mathfrak m$ lies over the maximal ideal of the fixed subring $B^{G}$ and that the residue extension of $B^{G}/\mathfrak m_{B^{G}}$ in $B/\mathfrak m$ is separable. Put $\ell = \#G$ and assume $\ell$ is prime. Let $t$ be a natural number such that the $t$-th lower ramification group, defined as the inertia subgroup of $\mathfrak m^{t+1}$ (the subgroup of $\sigma \in G$ acting trivially on $B/\mathfrak m^{t+1}$), is all of $G$, while the $(t+1)$-st, the inertia subgroup of $\mathfrak m^{t+2}$, is trivial. Write $\psi(n) = n$ if $n \le t$ and $\psi(n) = t + \ell\,(n-t)$ otherwise, and let $N(b) = \prod^{\mathrm f}_{\sigma \in G} \sigma \cdot b$ be the (finitely supported) product over $G$. Then for every natural number $n$ and every $b \in B$ both implications hold: if $b - 1 \in \mathfrak m^{\psi(n)}$ then $N(b) - 1 \in \mathfrak m^{\ell n}$, and if $b - 1 \in \mathfrak m^{\psi(n)+1}$ then $N(b) - 1 \in \mathfrak m^{\ell(n+1)}$.
--
--   This is the inclusion half of the classical statement that in a totally ramified layer of prime degree $\ell$ the norm carries the unit filtration level $\psi(n)$ of $B$ into the level $n$ of the fixed ring, $\psi$ being the Herbrand function of the layer, here in an abstract discrete-valuation-ring form with no completeness or cyclicity hypothesis beyond $\#G$ prime. It is used in the construction of the bound [`IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow`](thm.html#IsDiscreteValuationRing.exists_finset_card_mul_card_upperRamificationGroup_le_forall_exists_sub_mul_finprod_smul_mem_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.finprod_smul_sub_one_mem_maximalIdeal_pow_of_sub_one_mem_pow_herbrand_of_prime_card
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (n : ℕ) (b : B) :
    (b - 1 ∈ IsLocalRing.maximalIdeal B ^ (if n ≤ t then n else t + Nat.card G * (n - t)) →
        (∏ᶠ σ : G, σ • b) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * n)) ∧
    (b - 1 ∈ IsLocalRing.maximalIdeal B ^ ((if n ≤ t then n else t + Nat.card G * (n - t)) + 1) →
        (∏ᶠ σ : G, σ • b) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (n + 1))) := by sorry
