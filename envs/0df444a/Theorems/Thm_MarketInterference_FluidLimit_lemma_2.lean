-- Prove2me | Theorems.Thm_MarketInterference_FluidLimit_lemma_2
-- name    : MarketInterference.FluidLimit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:52.449956+00:00
-- url     : https://prove2.me/theorems/e0f09d54-a6db-4d03-ac87-af868203d3b1
-- title:
--   Lemma 2, p. 38 — for X_n ∼ Poisson(λn), Z = sup_{n ≥ 1} X_n/n has finite mean
-- statement:
--   Let $\lambda\ge 0$ and, on a probability space, let $X_1,X_2,\dots$ be random variables with $X_n\sim\mathrm{Poisson}(\lambda n)$ for every $n\ge 1$; no independence or other joint structure is assumed. Put $Y_n=\frac1n X_n$. Then
--
--   $$
--   Z=\sup_{n\ge 1} Y_n\quad\text{satisfies}\quad \mathbb E[Z]<\infty.
--   $$
--
--   In the proof of Theorem 1 this supplies an integrable dominating function for the scaled matching values.
--
--   **Formalization Note** The paper writes $Z=\max_{n=1}^\infty Y_n$; the maximum need not be attained, so $Z$ is the supremum, taken in $[0,\infty]$, and the conclusion is that its lower Lebesgue integral is finite. Each $X_n$ is a measurable $\mathbb N$-valued map whose law is $\mathrm{Poisson}(n\lambda)$.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 38, Lemma 2

import Mathlib

namespace MarketInterference.FluidLimit

open MeasureTheory ProbabilityTheory NNReal ENNReal

/-- Lemma 2 (arXiv:2205.02274v4, p. 38): if `X_n ∼ Poisson(λ n)` for every `n ≥ 1` (any joint law)
and `Y_n = X_n / n`, then `Z = sup_{n ≥ 1} Y_n` has a finite mean. -/
theorem lemma_2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (X : ℕ → Ω → ℕ)
    (hX : ∀ n : ℕ, 1 ≤ n → Measurable (X n) ∧ P.map (X n) = poissonMeasure ((n : ℝ≥0) * lam)) :
    ∫⁻ ω, (⨆ (n : ℕ) (_ : 1 ≤ n), ENNReal.ofReal ((X n ω : ℝ) / (n : ℝ))) ∂P < ⊤ := by sorry

end MarketInterference.FluidLimit
