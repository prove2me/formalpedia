-- Prove2me | Theorems.Thm_GaussMixHH_fact_5
-- name    : GaussMixHH.fact_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:28.548088+00:00
-- url     : https://prove2.me/theorems/45d3595a-1838-480f-bd2c-75bded0b4f85
-- title:
--   Fact 5, p.15 — the characteristic function of $\chi^2_n(\lambda)$ is $(1-2i\theta)^{-n/2}e^{\lambda i\theta/(1-2i\theta)}$
-- statement:
--   Let $n\in\mathbb N$, $\mu\in\mathbb R^n$ and $G\sim N(0,I_n)$, so that $\|G+\mu\|^2$ has the noncentral chi-squared law $\chi^2_n(\lambda)$ with $\lambda=\|\mu\|^2$. For every $\theta\in\mathbb R$,
--
--   $$\mathbb E\big[e^{i\theta\|G+\mu\|^2}\big]=(1-2i\theta)^{-n/2}\exp\Big(\|\mu\|^2\,\frac{i\theta}{1-2i\theta}\Big),$$
--
--   with the principal branch of the power.
--
--   This is the formula behind the radial identity (Lemma 12): conditioned on the center, the squared distance of an observation to the query point is noncentral chi-squared.
--
--   Differences from the source:
--   - encoding: the characteristic function of χ²_n(λ) → ∫ e^{iθ‖g+μ‖²} d stdGaussian(g) for every μ ∈ ℝⁿ (λ = ‖μ‖²); reason: χ²_n(λ) is defined on p.15 as the law of ‖G + μ‖² with ‖μ‖² = λ
--   - encoding: (1 − 2iθ)^{−n/2} → Complex.cpow with exponent −n/2 (principal branch); reason: Re(1 − 2iθ) = 1 > 0; the principal branch is the paper's
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Fact 5, eq. (5), p.15 (PDF p.17), citing [JKB95, Ch. 29]

import Mathlib
import Definitions.Def_GaussMixHH_RadialTransform

open MeasureTheory ProbabilityTheory Complex

namespace GaussMixHH

/-- **Fact 5** (characteristic function of the noncentral chi-squared distribution).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Fact 5, p.15 (PDF p.17), citing
[JKB95, Chapter 29]; the definition of `χ²_n(λ)` is on the same page.

"The characteristic function of χ²_n(λ), the chi-squared distribution with n degrees of freedom and
noncentrality parameter λ, is (1 − 2iθ)^{−n/2} e^{λ iθ/(1−2iθ)}." Here `χ²_n(λ)` is the law of
`∥G + μ∥²` with `G ∼ N(0, I_n)` and `∥μ∥² = λ`.

**Formalization Note.** Stated for every `n`, every `μ ∈ ℝⁿ` and every real `θ`, as the integral
of `e^{iθ∥G + μ∥²}` against Mathlib's `stdGaussian`. `(1 − 2iθ)^{−n/2}` is `gaussFactor n θ`
(principal branch) and `iθ/(1 − 2iθ)` is `wfun θ`. -/
theorem fact_5 (n : ℕ) (μ : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    ∫ g, cexp (I * θ * ((‖g + μ‖ ^ 2 : ℝ) : ℂ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      gaussFactor n θ * cexp (((‖μ‖ ^ 2 : ℝ) : ℂ) * wfun θ) := by sorry

end GaussMixHH
