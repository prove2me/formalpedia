-- Prove2me | Theorems.Thm_InfoRelaxTS_Gap_corollary_3
-- name    : InfoRelaxTS.Gap.corollary_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:40.57534+00:00
-- url     : https://prove2.me/theorems/0f256d09-cef4-4b90-a07b-7969f24202b3
-- title:
--   Corollary 3, p. 67 — a σ-sub-Gaussian variable satisfies (209) and hence (210)
-- statement:
--   Let $X$ be a real random variable on a probability space and $\sigma>0$. Suppose $X$ is $\sigma$-sub-Gaussian with variance proxy $\sigma^2$:
--   $$\mathbb E\big[\exp(\lambda(X-\mathbb EX))\big]\le\exp\Big(\frac{\sigma^2\lambda^2}{2}\Big)\qquad\text{for all }\lambda\in\mathbb R .$$
--   Then $X$ satisfies the tail condition of Lemma 4,
--   $$\mathbb P\big[X\ge\mathbb EX+z\sigma\big]\le e^{-z^2/2}\quad(z\ge0),$$
--   and hence
--   $$\mathbb E\Big[\big(X-(\mathbb EX+z\sigma)\big)^+\Big]\le\frac{\sigma}{z}\,e^{-z^2/2}\quad(z>0).$$
--
--   This is the form in which Lemma 4 is used for the sub-Gaussian mean-reward metrics of Lemma 5.
--
--   **Formalization Note** Definition 3 (p. 66) prints the bound $\exp(\sigma\lambda^2/2)$; every use in the paper ((213), (214) with $\sigma=\sqrt{L/\nu}$, (236)) has $\sigma^2$, and with the printed form the corollary would fail for $\sigma<1$. The statement uses Mathlib's `HasSubgaussianMGF` for $X-\mathbb EX$ with parameter $\sigma^2$, which also records that $e^{\lambda(X-\mathbb EX)}$ is integrable for every $\lambda$.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 66–67, Definition 3 (208), Corollary 3

import Mathlib

open MeasureTheory ProbabilityTheory

namespace InfoRelaxTS.Gap

theorem corollary_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hX : HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) ⟨σ ^ 2, sq_nonneg σ⟩ μ) :
    (∀ z : ℝ, 0 ≤ z →
      (μ {ω | (∫ x, X x ∂μ) + z * σ ≤ X ω}).toReal ≤ Real.exp (-z ^ 2 / 2)) ∧
    (∀ z : ℝ, 0 < z →
      ∫ ω, max (X ω - ((∫ x, X x ∂μ) + z * σ)) 0 ∂μ ≤ σ / z * Real.exp (-z ^ 2 / 2)) := by sorry

end InfoRelaxTS.Gap
