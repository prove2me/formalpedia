-- Prove2me | Theorems.Thm_GaussMixHH_lemma_12
-- name    : GaussMixHH.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:54.130213+00:00
-- url     : https://prove2.me/theorems/7bd4cc9f-6e74-4ae5-a95c-3500aac8be35
-- title:
--   Lemma 12, p.18 — the radial identity $\Phi_\rho(\theta)=(1-2i\theta)^{-n/2}\int_0^\infty e^{w(\theta)r^2}d\rho(r)$
-- statement:
--   Let $D$ be a probability measure on $\mathbb R^n$, $z\in\mathbb R^n$, and let $X=\mu+Z$ with $\mu\sim D$ and $Z\sim N(0,I_n)$ independent. Let $\rho$ be the law of $\|\mu-z\|$ and $w(\theta)=i\theta/(1-2i\theta)$. For every $\theta\in\mathbb R$,
--
--   $$\mathbb E\big[e^{i\theta\|X-z\|^2}\big]=(1-2i\theta)^{-n/2}\int_0^\infty e^{w(\theta)r^2}\,d\rho(r).\tag{6}$$
--
--   The left side is the characteristic function $\Phi_\rho(\theta)$ of the observed squared distance. The identity shows that it depends on $D$ only through the radial law $\rho$, which is what lets the algorithm reason about centers near $z$ from samples.
--
--   Differences from the source:
--   - generalization: D the discrete center distribution of the model → D any Borel probability measure on ℝⁿ; reason: the identity holds for every D; the discrete D of the paper is a special case
--   - encoding: Φρ(θ) = E[e^{iθ‖X−z‖²}] with X = μ + Z → the integral of e^{iθ‖x−z‖²} against D ∗ N(0, I_n); reason: D ∗ N(0, I_n) is the law of μ + Z with μ, Z independent
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 12, eq. (6), p.18 (PDF p.20); eq. (3), p.9

import Mathlib
import Definitions.Def_GaussMixHH_RadialTransform
import Definitions.Def_GaussMixHH_CenterModel

open MeasureTheory ProbabilityTheory Complex

namespace GaussMixHH

/-- **Lemma 12** (A radial identity).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 12, eq. (6), p.18 (PDF p.20);
`Φ_ρ(θ) = E[e^{iθ∥X−z∥²}]` is eq. (3), p.9.

"Let X = μ + Z, where μ ∼ D and Z ∼ N(0, I_n) are independent, and let ρ be the probability
distribution of ∥μ − z∥. For every θ ∈ R, writing w(θ) := iθ/(1 − 2iθ), we have
Φ_ρ(θ) = (1 − 2iθ)^{−n/2} ∫_0^∞ e^{w(θ)r²} dρ(r)."

**Formalization Note.** The law of `X` is `mixture D = D ∗ N(0, I_n)`, and the left side is
`E[e^{iθ∥X−z∥²}]`. `PhiRad n ρ θ` is the right side of (6). `D` is any Borel probability measure on
`ℝⁿ`, not only a discrete one (a generalization; the identity does not use discreteness). -/
theorem lemma_12 (n : ℕ) (D : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure D]
    (z : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    ∫ x, cexp (I * θ * ((‖x - z‖ ^ 2 : ℝ) : ℂ)) ∂(mixture D) = PhiRad n (radialLaw D z) θ := by sorry

end GaussMixHH
