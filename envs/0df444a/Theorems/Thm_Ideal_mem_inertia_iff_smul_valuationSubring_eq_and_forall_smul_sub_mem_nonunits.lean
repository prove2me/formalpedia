-- Prove2me | Theorems.Thm_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
-- name    : Ideal.mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/45caa288-a7b9-5573-b91c-db348dba4d16
-- title:
--   Inertia at an ideal equals inertia at its centred place
-- statement:
--   Let $G$ be a group acting by ring automorphisms on a commutative ring $B$ and on a field $F$, let $\rho : B \to F$ be a ring homomorphism that is $G$-equivariant in the sense that $g \cdot \rho(b) = \rho(g \cdot b)$ for all $g \in G$, $b \in B$, let $\mathfrak{y}$ be an ideal of $B$ and let $P$ be a valuation subring of $F$. Assume: $\rho(b) \in P$ for every $b \in B$; $\rho(b)$ lies in `P.nonunits`, the set of elements of $F$ of $P$-valuation $<1$, that is, the maximal ideal of $P$, exactly when $b \in \mathfrak{y}$; $P$ is the only valuation subring $P'$ of $F$ with these two properties, i.e. with $\rho(B) \subseteq P'$ and $\rho^{-1}(\mathfrak{m}_{P'}) = \mathfrak{y}$; and every $e \in P$ satisfies $e - \rho(b) \in \mathfrak{m}_P$ for some $b \in B$, so that $\rho(B)$ meets every residue class of $P$. Then for each $g \in G$, $g$ belongs to the inertia subgroup $\mathfrak{y}.\mathrm{inertia}\ G$, that is, $g \cdot b - b \in \mathfrak{y}$ for all $b \in B$, if and only if the pointwise translate $g \cdot P$ equals $P$ and $g \cdot e - e \in \mathfrak{m}_P$ for every $e \in P$.
--
--   This is the dictionary, in the classical decomposition–inertia setting of a valuation in a Galois situation, between the inertia group of an ideal of $B$ and the inertia group of the unique place of $F$ centred on that ideal and having $\rho(B)$ as a full set of residue representatives. It is used in the analysis of the diamond action on integral models of modular curves, notably to identify inertia at a supersingular point of a special fibre, and in the construction of torsion points on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
    {B : Type*} [CommRing B] {F : Type*} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G B] [MulSemiringAction G F]
    (ρ : B →+* F) (hρ : ∀ (g : G) (b : B), g • ρ b = ρ (g • b))
    (𝔶 : Ideal B) (P : ValuationSubring F)
    (hP : ∀ b : B, ρ b ∈ P) (hPy : ∀ b : B, ρ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F,
      (∀ b : B, ρ b ∈ P') → (∀ b : B, ρ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ b : B, (e : F) - ρ b ∈ P.nonunits)
    (g : G) :
    g ∈ 𝔶.inertia G ↔ (g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits) := by sorry
