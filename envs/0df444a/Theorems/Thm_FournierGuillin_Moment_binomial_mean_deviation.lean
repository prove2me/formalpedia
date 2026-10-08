-- Prove2me | Theorems.Thm_FournierGuillin_Moment_binomial_mean_deviation
-- name    : FournierGuillin.Moment.binomial_mean_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:11.943032+00:00
-- url     : https://prove2.me/theorems/907fe6db-77c0-4f94-b513-16930877eb4e
-- title:
--   Proof of Theorem 1, p. 8 — E|μ_N(A) − μ(A)| ≤ min{2μ(A), √(μ(A)/N)}
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^d$, let $X_1,\dots,X_N$ ($N\ge1$) be i.i.d. with law $\mu$, and let $\mu_N=\frac1N\sum_{k=1}^N\delta_{X_k}$ be their empirical measure. For every Borel set $A\subset\mathbb R^d$,
--   $$\mathbb E\big|\mu_N(A)-\mu(A)\big|\le\min\Big\{2\mu(A),\sqrt{\mu(A)/N}\Big\}.$$
--   Since $N\mu_N(A)$ is Binomial$(N,\mu(A))$-distributed, this is a mean-deviation bound for the binomial law, the basic probabilistic input of the moment estimates.
--
--   **Formalization Note** The sample is a point $\omega$ of $(\mathbb R^d)^N$ under the product measure $\mu^{\otimes N}$; these are the first $N$ terms of the paper's i.i.d. sequence. The expectation is the lower Lebesgue integral of a $[0,\infty]$-valued function, which here is measurable.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Proof of Theorem 1, p. 8, first display

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- Proof of Theorem 1, p. 8, first display: for a Borel set `A ⊂ ℝᵈ`, since `Nμ_N(A)` is
Binomial`(N, μ(A))`, `E|μ_N(A) − μ(A)| ≤ min{2μ(A), √(μ(A)/N)}`. The sample `X₁, …, X_N` is
`ω : Fin N → ℝᵈ` under the product measure `μ^{⊗N}`, and `μ_N` is its empirical distribution. -/
theorem binomial_mean_deviation {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] {A : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A)
    {N : ℕ} (hN : 1 ≤ N) :
    ∫⁻ ω, ENNReal.ofReal
        |(WassersteinDRO.Duality.empiricalDistribution ω A).toReal - (μ A).toReal|
        ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ENNReal.ofReal (min (2 * (μ A).toReal) (Real.sqrt ((μ A).toReal / N))) := by sorry

end FournierGuillin.Moment
