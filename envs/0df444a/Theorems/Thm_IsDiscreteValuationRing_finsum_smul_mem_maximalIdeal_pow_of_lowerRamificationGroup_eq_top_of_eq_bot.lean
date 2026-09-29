-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
-- name    : IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/87fc45b5-bf2f-5338-82db-0716c0311cf3
-- title:
--   Trace estimate in a one-jump ramification filtration
-- statement:
--   Let $B$ be a commutative domain that is a discrete valuation ring, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal B`, and let $G$ be a finite group acting on $B$ by ring automorphisms, the action being faithful. Write $A =$ `FixedPoints.subring B G` for the fixed subring; assume that $\mathfrak m$ lies over the maximal ideal of $A$ and that the residue field extension $B/\mathfrak m$ over $A/\mathfrak m_A$ is separable. Let $t$ be a natural number such that the $t$-th lower ramification group of the action, namely the inertia subgroup of $\mathfrak m^{t+1}$ in $G$ (the $\sigma \in G$ acting trivially on $B/\mathfrak m^{t+1}$), is all of $G$, while the $(t+1)$-st lower ramification group, the inertia subgroup of $\mathfrak m^{t+2}$, is trivial. Then for every natural number $m$ and every $x \in \mathfrak m^{m}$, the sum $\sum_{\sigma \in G} \sigma \cdot x$ lies in $\mathfrak m^{\,|G|\,\lfloor (m + (t+1)(|G|-1))/|G| \rfloor}$, where $|G| =$ `Nat.card G`, and the subtraction and division are those of the natural numbers. Only this inclusion is asserted, not the corresponding equality of ideals.
--
--   This is the classical estimate for the trace map in a totally ramified extension of discrete valuation rings whose lower ramification filtration has a single jump, at $t$: deep elements have deep traces, the exponent being governed by the different exponent $(t+1)(|G|-1)$. It is used in the project's analysis of the Galois module structure of such a layer, feeding the results on products of conjugates and on elements congruent to $1$ modulo powers of $\mathfrak m$ when $|G|$ is prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (m : ℕ) (x : B) (hx : x ∈ IsLocalRing.maximalIdeal B ^ m) :
    ∑ᶠ σ : G, σ • x ∈
      IsLocalRing.maximalIdeal B ^ (Nat.card G * ((m + (t + 1) * (Nat.card G - 1)) / Nat.card G)) := by sorry
