-- Prove2me | Theorems.Thm_InfoRelaxTS_Gap_lemma_4
-- name    : InfoRelaxTS.Gap.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:37.125129+00:00
-- url     : https://prove2.me/theorems/74ffe1b8-1c42-4eb0-bbf1-6b45a5799a54
-- title:
--   Lemma 4, pp. 66–67 — a Gaussian tail gives 𝔼[(X − (𝔼X + zσ))⁺] ≤ (σ/z)e^{−z²/2}
-- statement:
--   Let $X$ be an integrable real random variable on a probability space, and suppose there is $\sigma>0$ with
--   $$\mathbb P\big[X\ge\mathbb EX+z\sigma\big]\le e^{-z^2/2}\qquad\text{for all }z\ge0 .$$
--   Then
--   $$\mathbb E\Big[\big(X-(\mathbb EX+z\sigma)\big)^+\Big]\le\frac{\sigma}{z}\,e^{-z^2/2}\qquad\text{for all }z>0 .$$
--
--   The bound converts a Gaussian-type tail into a bound on the expected overshoot above a confidence level; Theorem 3 applies it with $z=\sqrt{2\log T}$ to the mean-reward metrics.
--
--   **Formalization Note** The page speaks of "a random variable $X$" and its mean $\mathbb EX$; integrability of $X$ and a probability measure are made explicit. $(x)^+=\max(x,0)$.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 66–67, Lemma 4, (209)–(210)

import Mathlib

open MeasureTheory

namespace InfoRelaxTS.Gap

theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (σ : ℝ) (hσ : 0 < σ)
    (htail : ∀ z : ℝ, 0 ≤ z →
      (μ {ω | (∫ x, X x ∂μ) + z * σ ≤ X ω}).toReal ≤ Real.exp (-z ^ 2 / 2)) :
    ∀ z : ℝ, 0 < z →
      ∫ ω, max (X ω - ((∫ x, X x ∂μ) + z * σ)) 0 ∂μ ≤ σ / z * Real.exp (-z ^ 2 / 2) := by sorry

end InfoRelaxTS.Gap
