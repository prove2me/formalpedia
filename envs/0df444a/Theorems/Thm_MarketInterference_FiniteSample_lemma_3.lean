-- Prove2me | Theorems.Thm_MarketInterference_FiniteSample_lemma_3
-- name    : MarketInterference.FiniteSample.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:53.705138+00:00
-- url     : https://prove2.me/theorems/1c0f1050-5fef-4f44-bb70-7ae44f5989e4
-- title:
--   Lemma 3, p. 51 — ∂/∂λ E[g(x, D)] = E[g(x, D+1) − g(x, D)] for D ∼ Poisson(λ)
-- statement:
--   Let $x\in\mathbb R^m$ be a fixed vector and let $g:\mathbb R^m\times\mathbb N\to\mathbb R$ be continuous in its first argument and satisfy
--   $$
--   0\le g(y,d)\le M\big(|d|+\|y\|_1\big)\qquad\text{for all }y\in\mathbb R^m,\ d\in\mathbb N .
--   $$
--   For $D\sim\mathrm{Poisson}(\lambda)$, the map $\lambda\mapsto\mathbb E[g(x,D)]$ is differentiable at every $\lambda_0\in(0,\infty)$, with
--   $$
--   \frac{\partial}{\partial\lambda}\mathbb E[g(x,D)]\Big|_{\lambda=\lambda_0}=\mathbb E\big[g(x,D+1)-g(x,D)\big],\qquad D\sim\mathrm{Poisson}(\lambda_0).
--   $$
--
--   This is the one-dimensional derivative formula behind the partial derivatives of the expected matching value (Lemma 4).
--
--   **Formalization Note** $\|y\|_1=\sum_k|y_k|$ and $|d|=d$ for $d\in\mathbb N$. The Poisson mean is passed through `Real.toNNReal`, which is inactive near $\lambda_0>0$, so the map is defined on a neighbourhood of $\lambda_0$. The paper's continuity of $g$ is kept as continuity in the vector argument for each $d$ (continuity in $d\in\mathbb N$ is vacuous).
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 51, Lemma 3

import Mathlib

namespace MarketInterference.FiniteSample

open MeasureTheory ProbabilityTheory

theorem lemma_3 {m : ℕ} (x : Fin m → ℝ) (g : (Fin m → ℝ) → ℕ → ℝ) (M : ℝ)
    (hcont : ∀ d, Continuous fun y => g y d)
    (hg : ∀ y d, 0 ≤ g y d ∧ g y d ≤ M * ((d : ℝ) + ∑ k, |y k|))
    (l₀ : ℝ) (hl₀ : 0 < l₀) :
    HasDerivAt (fun l : ℝ => ∫ d, g x d ∂(poissonMeasure (Real.toNNReal l)))
      (∫ d, (g x (d + 1) - g x d) ∂(poissonMeasure (Real.toNNReal l₀))) l₀ := by sorry

end MarketInterference.FiniteSample
