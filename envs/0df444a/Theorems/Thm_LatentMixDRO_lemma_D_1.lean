-- Prove2me | Theorems.Thm_LatentMixDRO_lemma_D_1
-- name    : LatentMixDRO.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:23:44.273528+00:00
-- url     : https://prove2.me/theorems/5c0fcd4e-cdab-4d8e-95d1-ec31189edd50
-- title:
--   Lemma D.1 — duality for conditional value-at-risk
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space, $W$ an integrable random variable and $\alpha_0\in(0,\tfrac12)$. Then
--
--   $$
--   \sup_{\mathcal L}\Big\{\mathbb E[\mathcal L W]\ \Big|\ \mathcal L:\Omega\to[0,\tfrac1{\alpha_0}]\text{ measurable},\ \mathbb E[\mathcal L]=1\Big\}=\inf_{\eta\in\mathbb R}\Big\{\frac1{\alpha_0}\mathbb E\big[(W-\eta)_+\big]+\eta\Big\}.
--   $$
--
--   This identifies the supremum over bounded likelihood ratios with the Rockafellar–Uryasev form of conditional value-at-risk, and is the source of the dual objective (7).
--
--   Differences from the source:
--   - encoding: $\sup=\inf$ of two real quantities → `IsLUB` and `IsGLB` of one common value $v$; reason: Lean convention; the suprema of real sets are otherwise junk-valued on unbounded sets
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Lemma D.1, p.33

import Mathlib

open MeasureTheory

namespace LatentMixDRO

/-- Lemma D.1: duality for conditional value-at-risk. For an integrable `W` on a probability space,
`sup {E[𝓛 W] | 𝓛 : Ω → [0, 1/α₀] measurable, E[𝓛] = 1} = inf_{η ∈ ℝ} {(1/α₀) E[(W - η)₊] + η}`.

Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures,
arXiv:2007.13982v2, Lemma D.1, p.33.

**Formalization Note.** The supremum and the infimum are stated as `IsLUB` and `IsGLB` of one common
value `v`, so no junk value of a real `sSup`/`sInf` enters. -/
theorem lemma_D_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → ℝ) (hW : Integrable W μ) (α₀ : ℝ) (hα₀ : 0 < α₀) (hα₀' : α₀ < 1 / 2) :
    ∃ v : ℝ,
      IsLUB {s | ∃ 𝓛 : Ω → ℝ, Measurable 𝓛 ∧ (∀ a, 0 ≤ 𝓛 a ∧ 𝓛 a ≤ 1 / α₀) ∧
        (∫ a, 𝓛 a ∂μ) = 1 ∧ s = ∫ a, 𝓛 a * W a ∂μ} v ∧
      IsGLB {s | ∃ η : ℝ, s = (1 / α₀) * (∫ a, max (W a - η) 0 ∂μ) + η} v := by sorry

end LatentMixDRO
