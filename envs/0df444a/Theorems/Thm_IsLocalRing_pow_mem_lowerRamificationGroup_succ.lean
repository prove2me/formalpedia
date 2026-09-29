-- Prove2me | Theorems.Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ
-- name    : IsLocalRing.pow_mem_lowerRamificationGroup_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/19486382-891e-50f6-9492-93db354dc2cf
-- title:
--   p-th powers in lower ramification groups
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m =$ `maximalIdeal R`, and let $G$ be a group acting on $R$ by ring automorphisms (a `MulSemiringAction`). For $i \in \mathbb{N}$, the subgroup `lowerRamificationGroup R G i` of $G$ is by definition the inertia subgroup of the ideal $\mathfrak m^{i+1}$, that is, the set of $\sigma \in G$ with $\sigma \cdot x - x \in \mathfrak m^{i+1}$ for every $x \in R$. The hypotheses are: a natural number $p$ whose image in $R$ lies in $\mathfrak m$; an index $i$ with $1 \le i$; and an element $\sigma \in G$ lying in `lowerRamificationGroup R G i`, i.e. $\sigma \cdot x - x \in \mathfrak m^{i+1}$ for all $x \in R$. The conclusion is that $\sigma^p$ lies in `lowerRamificationGroup R G (i+1)`, i.e. $\sigma^p \cdot x - x \in \mathfrak m^{i+2}$ for every $x \in R$. Note that $p$ is an arbitrary natural number subject only to the condition $(p : R) \in \mathfrak m$; primality is not assumed.
--
--   This is the exponent form of the standard fact that the graded quotients $G_i/G_{i+1}$ for $i \ge 1$ are killed by the residue characteristic (Serre, Local Fields IV §2, consequences of Proposition 7), here in the general setting of a local ring with a ring action rather than a local field extension. It is used to show that the first lower ramification group is a $p$-group and, via that, in the computation relating the conductor exponent to the dimension of the inertia invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise commutatorElement
open IsLocalRing

theorem IsLocalRing.pow_mem_lowerRamificationGroup_succ {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    {p : ℕ} (hp : (p : R) ∈ maximalIdeal R) {i : ℕ} (hi : 1 ≤ i) {σ : G}
    (hσ : σ ∈ lowerRamificationGroup R G i) :
    σ ^ p ∈ lowerRamificationGroup R G (i + 1) := by sorry
