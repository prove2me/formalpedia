-- Prove2me | Theorems.Thm_MarketInterference_FiniteSample_lemma_5
-- name    : MarketInterference.FiniteSample.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:55.892508+00:00
-- url     : https://prove2.me/theorems/71467ee1-785c-4e54-84df-1bd15a42fc60
-- title:
--   Lemma 5, p. 53 — Poisson size-bias identity E[D f(D)] = λ E[f(D+1)]
-- statement:
--   Let $D\sim\mathrm{Poisson}(\lambda)$ with $\lambda\ge0$, and let $f:\mathbb N\to\mathbb R$ satisfy $\mathbb E[|f(D)|]<\infty$. Then
--   $$
--   \mathbb E[D f(D)]=\lambda\,\mathbb E[f(D+1)].
--   $$
--
--   In the proof of Theorem 6 this identity, applied to the total demand of one type, turns the negative-demand subgradient $A^-_i$ weighted by $D_i$ into the positive-demand subgradient $A^+_i$.
--
--   **Formalization Note** The hypothesis "$\mathbb E[f(D)]<\infty$" is read as integrability of $f$ under $\mathrm{Poisson}(\lambda)$. Expectations are Bochner integrals; for $\lambda>0$, $d\mapsto d f(d)$ is integrable exactly when $d\mapsto f(d+1)$ is, so the two sides are never compared through a one-sided junk value.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 53, Lemma 5

import Mathlib

namespace MarketInterference.FiniteSample

open MeasureTheory ProbabilityTheory NNReal

theorem lemma_5 (r : ℝ≥0) (f : ℕ → ℝ) (hf : Integrable f (poissonMeasure r)) :
    ∫ d, (d : ℝ) * f d ∂(poissonMeasure r) = (r : ℝ) * ∫ d, f (d + 1) ∂(poissonMeasure r) := by sorry

end MarketInterference.FiniteSample
