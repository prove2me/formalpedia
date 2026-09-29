-- Prove2me | Theorems.Thm_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt
-- name    : IsLocalRing.forall_mem_upperRamificationGroup_iff_finsum_indicator_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/0f4556e3-2325-5486-b356-a0e6ff459b8c
-- title:
--   Character kills Γ^u iff its Swan sum is <u
-- statement:
--   Let $R$ be a commutative local ring and let $\Gamma$ be a finite group acting on $R$ by ring automorphisms, and write $\Gamma_i =$ [`IsLocalRing.lowerRamificationGroup R Γ i`](def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) for the inertia subgroup of $\Gamma$ on the ideal $\mathfrak m_R^{\,i+1}$, i.e. the subgroup of those $\sigma$ acting trivially modulo $\mathfrak m_R^{\,i+1}$. Let $A$ be a commutative group and $\chi \colon \Gamma \to A$ a group homomorphism. Assume there is some $N \in \mathbb{N}$ with $\chi$ trivial on $\Gamma_N$, and that $\chi$ is not trivial on $\Gamma_0$. Let $u \in \mathbb{Q}$ with $0 \le u$. For the upper group one has $\Gamma^u = \Gamma_{n(u)}$ with $n(u) = \inf\{n \in \mathbb{N} : u \le \varphi(n)\}$, where $\varphi =$ [`IsLocalRing.herbrandPhi R Γ`](def/Mathlib_RingTheory_Valuation_UpperRamificationGroup.html#L34) is the Herbrand function of the filtration. The assertion is the equivalence: $\chi$ is trivial on every element of $\Gamma^u$ if and only if
--   $$\sum^{\mathrm f}_{i \in \mathbb{N}} \frac{\#\Gamma_{i+1}}{\#\Gamma_0}\cdot\bigl[\chi|_{\Gamma_{i+1}} \ne 1\bigr] < u,$$
--   the sum being a `finsum` over all natural numbers $i$ of the indicated ratios of cardinalities weighted by $0$ or $1$ according as $\chi$ is or is not trivial on $\Gamma_{i+1}$.
--
--   This is the comparison, for a one-dimensional character, between the Swan sum $\mathrm{sw}(\chi) = \sum_{i\ge 1}[\Gamma_i : 1]/[\Gamma_0:1]\,[\chi|_{\Gamma_i}\ne 1]$ and the upper (Herbrand-numbered) ramification filtration: $\mathrm{sw}(\chi)$ is the unique upper jump of $\chi$, so $\chi$ kills $\Gamma^u$ exactly for $u > \mathrm{sw}(\chi)$. It is used in the abelian local theory to identify the Swan conductor and the conductor exponent of a character with its upper ramification break, via [`ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt`](thm.html#ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_iff_swanConductor_lt), [`ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le`](thm.html#ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le) and [`ArtinL.Abelian.natCeil_swanConductor_eq`](thm.html#ArtinL.Abelian.natCeil_swanConductor_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_forall_mem_upperRamificationGroup_iff_finsum_indicator_lt.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Classical in

theorem IsLocalRing.forall_mem_upperRamificationGroup_iff_finsum_indicator_lt
    {R : Type*} [CommRing R] [IsLocalRing R] {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ R]
    {A : Type*} [CommGroup A] (χ : Γ →* A)
    (hfin : ∃ N : ℕ, ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ N, χ σ = 1)
    (hram : ¬ ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ 0, χ σ = 1)
    (u : ℚ) (hu : 0 ≤ u) :
    (∀ σ ∈ IsLocalRing.upperRamificationGroup R Γ u, χ σ = 1) ↔
      ∑ᶠ i : ℕ,
          (Nat.card (IsLocalRing.lowerRamificationGroup R Γ (i + 1)) : ℚ) /
              (Nat.card (IsLocalRing.lowerRamificationGroup R Γ 0) : ℚ) *
            (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R Γ (i + 1), χ σ = 1 then 0 else 1) < u := by sorry
