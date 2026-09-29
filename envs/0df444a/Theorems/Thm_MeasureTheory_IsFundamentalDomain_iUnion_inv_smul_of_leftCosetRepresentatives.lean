-- Prove2me | Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
-- name    : MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/5c91be15-c79a-5475-a27f-c3c125909228
-- title:
--   Fundamental domain for a subgroup from coset representatives
-- statement:
--   Let $G$ be a group acting on a measurable space $X$, with a measure $\mu$ on $X$, a measurable structure on $G$ making the action measurable in each variable and $\mu$ invariant under the action. Let $\Gamma_1,\Gamma_2$ be subgroups of $G$ with $\Gamma_2 \le \Gamma_1$, with $\Gamma_1$ countable, and let $\mathcal{F} \subseteq X$ be a fundamental domain for the action of $\Gamma_1$ on $X$ in Mathlib's sense: $\mathcal{F}$ is null measurable, almost every $x \in X$ satisfies $\gamma \cdot x \in \mathcal{F}$ for some $\gamma \in \Gamma_1$, and the translates $\gamma \cdot \mathcal{F}$, $\gamma \in \Gamma_1$, are pairwise almost everywhere disjoint. Let $\iota$ be a countable index type and $R : \iota \to \Gamma_1$ a family such that for every $\gamma \in \Gamma_1$ there is exactly one index $i$ with $R_i^{-1}\gamma \in \Gamma_2$, i.e. the $R_i$ represent the cosets in $\Gamma_1/\Gamma_2$ without repetition. Then the set $\bigcup_{i \in \iota} R_i^{-1} \cdot \mathcal{F}$ is a fundamental domain for the action of $\Gamma_2$ on $X$ with respect to $\mu$, in the same sense.
--
--   This is the standard passage from a fundamental domain for a group to one for a subgroup of finite or countable index, the geometric form of the decomposition $\Gamma_1 = \bigsqcup_i R_i\Gamma_2$. It underlies the unfolding steps for integrals of automorphic forms, where an integral over $\Gamma_1 \backslash X$ of a sum over cosets is rewritten as an integral over $\Gamma_2 \backslash X$; it is used in the treatment of Petersson-type integrals, Bruhat decompositions and pseudo-Eisenstein series in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise ENNReal

theorem MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    IsFundamentalDomain Γ₂ (⋃ i, ((R i : G)⁻¹) • 𝓕) μ := by sorry
