-- Prove2me | Theorems.Thm_LatentRobust_gaussian_pdf_le
-- name    : LatentRobust.gaussian_pdf_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:33.676981+00:00
-- url     : https://prove2.me/theorems/1fb4cb9e-7930-4123-a2b5-d30ac594b6b1
-- title:
--   App. A.3, p.22 — the $\mathsf N(\nu,\sigma)$ density is at most $1/\sqrt{2\pi\sigma}$
-- statement:
--   For every mean $\nu\in\mathbb R$, every variance $\sigma>0$ and every $u\in\mathbb R$, the density of the normal law $\mathsf N(\nu,\sigma)$ satisfies
--   $$
--   \frac{1}{\sqrt{2\pi\sigma}}\exp\Big(-\frac{(u-\nu)^2}{2\sigma}\Big)\le\frac{1}{\sqrt{2\pi\sigma}} .
--   $$
--
--   It bounds the probability that a normal variable falls into a short interval by the interval's length times $1/\sqrt{2\pi\sigma}$, which turns the slab probabilities of the closed-form step into (19).
--
--   Differences from the source:
--   - reading: N(ν, σ) with density bound 1/√(2πσ) → σ is the variance (Mathlib's gaussianPDFReal ν σ); reason: the page applies the bound to N(a, a) with a a variance, and 1/√(2πσ) is the density's maximum exactly when σ is the variance
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, App. A.3 (proof of Theorem 3.1), p.22, "the pdf of normal N(ν, σ) is bounded by 1/√2πσ"

import Mathlib

namespace LatentRobust

open ProbabilityTheory

/-- **Gaussian density bound** (Javanmard, Mehrabi, arXiv:2110.11950v2, App. A.3, p.22): "the pdf of normal `N(ν, σ)` is
bounded by `1/√(2πσ)`, for any values of `σ > 0` and `ν`".

**Formalization Note** As on the page (which applies it to `N(a, a)`, `a` a variance), the
second parameter `σ` is the variance; Mathlib's `gaussianPDFReal ν v` is the density of the
normal law with mean `ν` and variance `v`. -/
theorem gaussian_pdf_le (ν : ℝ) (v : NNReal) (hv : 0 < v) (x : ℝ) :
    gaussianPDFReal ν v x ≤ 1 / Real.sqrt (2 * Real.pi * v) := by sorry

end LatentRobust
