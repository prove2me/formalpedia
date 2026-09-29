-- Prove2me | Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
-- name    : MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/e93d0863-497e-55cc-84f5-a8ca191a4f2c
-- title:
--   Unfolding an integral over coset translates of a fundamental domain
-- statement:
--   Let $G$ be a group with a measurable space structure acting on a measurable space $X$ by a measurable scalar action, let $\mu$ be a measure on $X$ invariant under this action, and let $\iota$ be a countable index type. Let $\Gamma_1, \Gamma_2 \le G$ be subgroups with $\Gamma_2 \le \Gamma_1$ and $\Gamma_1$ countable, and let $\mathcal{F} \subseteq X$ be a fundamental domain for the action of $\Gamma_1$ on $X$ with respect to $\mu$. Let $R : \iota \to \Gamma_1$ be a family such that for every $\gamma \in \Gamma_1$ there is exactly one index $i$ with $(R\,i)^{-1}\gamma \in \Gamma_2$, i.e. $R$ picks out one element from each left coset $R\,i\cdot\Gamma_2$ meeting $\Gamma_1$. Write $\mathcal{F}_2 = \bigcup_i (R\,i)^{-1}\cdot\mathcal{F}$. Then two statements hold. First, for every measurable $f : X \to [0,\infty]$, $\int_{\mathcal{F}_2} f \,d\mu = \int_{\mathcal{F}} \sum_i f((R\,i)^{-1}x)\,d\mu(x)$ as lower Lebesgue integrals. Second, for every Banach space $E$ over $\mathbb{R}$ and every $\mu$-a.e. strongly measurable $h : X \to E$ satisfying $\int_{\mathcal{F}} \sum_i \|h((R\,i)^{-1}x)\|\,d\mu(x) < \infty$ (the inner sum and integral taken in $[0,\infty]$): $h$ is integrable on $\mathcal{F}_2$; for $\mu$-almost every $x \in \mathcal{F}$ the family $i \mapsto \|h((R\,i)^{-1}x)\|$ is summable; and $\int_{\mathcal{F}_2} h \,d\mu = \int_{\mathcal{F}} \sum_i h((R\,i)^{-1}x)\,d\mu(x)$ as Bochner integrals.
--
--   This is the measure-theoretic core of the unfolding step (Rankin's trick): an integral over a union of translates of a fundamental domain for the larger group is rewritten as an integral over that fundamental domain of the sum over coset representatives. No invariance of $f$ or $h$ is required; it is used in the construction and estimation of pseudo-Eisenstein series and in Iwasawa-type decompositions of adelic integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise ENNReal

theorem MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    (∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, f x ∂μ = ∫⁻ x in 𝓕, ∑' i, f ((R i : G)⁻¹ • x) ∂μ) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (h : X → E),
      AEStronglyMeasurable h μ →
      ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ < ∞ →
      IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ ∧
      (∀ᵐ x ∂μ.restrict 𝓕, Summable fun i => ‖h ((R i : G)⁻¹ • x)‖) ∧
      ∫ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, h x ∂μ = ∫ x in 𝓕, ∑' i, h ((R i : G)⁻¹ • x) ∂μ := by sorry
