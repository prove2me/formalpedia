-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one
-- name    : IsDiscreteValuationRing.ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/7aac91c4-6e13-5b7d-bc04-fa095d30448f
-- title:
--   Sen's congruence for ramification depths of p-power iterates
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $G$ be a group acting on $R$ by ring automorphisms (a `MulSemiringAction`) in such a way that the action is faithful. Let $p$ be a prime number whose image in $R$ lies in the maximal ideal $\mathfrak m$ of $R$, and assume the residue field $R/\mathfrak m$ is perfect. For $\tau \in G$ the ramification depth is the infimum, taken in $\mathbb N \cup \{\infty\}$, of the additive valuations $\mathrm{addVal}_R(\tau \cdot x - x)$ over all $x \in R$. Let $\sigma \in G$ lie in the first lower ramification group, i.e. in the inertia subgroup of the ideal $\mathfrak m^{2}$: $\sigma \cdot x - x \in \mathfrak m^{2}$ for every $x \in R$. Let $n \ge 1$ be an integer with $\sigma^{p^{n}} \ne 1$. Then the natural numbers obtained from the ramification depths of $\sigma^{p^{\,n-1}}$ and of $\sigma^{p^{\,n}}$ by the truncation $\mathbb N \cup \{\infty\} \to \mathbb N$ (which sends $\infty$ to $0$) are congruent modulo $p^{n}$.
--
--   This is Sen's congruence on the ramification depths of the successive $p$-power iterates of a wildly ramified automorphism of a discrete valuation ring with perfect residue field; no completeness of $R$ is assumed, the depths being unchanged by completion. It is the arithmetic input to [`IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic`](thm.html#IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isCyclic), and hence to the Hasse–Arf theorem for cyclic $p$-groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
import Definitions.Def_RamificationChain_Wild

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R)
    [PerfectField (IsLocalRing.ResidueField R)]
    {σ : G} (hσ : σ ∈ IsLocalRing.lowerRamificationGroup R G 1)
    {n : ℕ} (hn : 1 ≤ n) (hσn : σ ^ p ^ n ≠ 1) :
    (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ (n - 1))).toNat ≡
      (IsDiscreteValuationRing.ramificationDepth R G (σ ^ p ^ n)).toNat [MOD p ^ n] := by sorry
