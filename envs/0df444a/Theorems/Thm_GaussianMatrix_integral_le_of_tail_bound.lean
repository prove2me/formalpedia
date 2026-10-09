-- Prove2me | Theorems.Thm_GaussianMatrix_integral_le_of_tail_bound
-- name    : GaussianMatrix.integral_le_of_tail_bound
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:50:25.766812+00:00
-- url     : https://prove2.me/theorems/a1972394-8f2b-4b92-986a-9fe35f97eeae
-- title:
--   Expectation bound from a polynomial tail: $\mathbb P\{X>t\}\le C t^{-m}$ with $m>1$ implies $\mathbb E X\le C^{1/m}\,\frac{m}{m-1}$
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space and let $X:\Omega\to\mathbb R$ be an (almost everywhere) measurable random variable with $X\ge 0$ almost surely. Let $C>0$ and $m>1$ be real constants, and suppose that $X$ has the polynomial tail bound
--   $$\mu\{\omega : X(\omega)>t\}\;\le\; C\,t^{-m}\qquad\text{for every } t>0 .$$
--   Then $X$ is integrable and
--   $$\mathbb E\,X=\int_\Omega X\,d\mu\;\le\; C^{1/m}\,\frac{m}{m-1}.$$
--
--   The proof is the layer-cake formula $\mathbb E X=\int_0^\infty \mu\{X>t\}\,dt$, splitting the integral at $a=C^{1/m}$ (the point where the tail bound equals $1$): on $(0,a]$ the probability is bounded by $1$, and on $(a,\infty)$ by $Ct^{-m}$, which integrates to $C a^{1-m}/(m-1)=a/(m-1)$.
--
--   This lemma converts a tail bound into a moment bound in a form usable on any probability space; in the Gaussian-matrix series it turns the tail bound for $\|G^\dagger\|$ into the expectation bound $\mathbb E\|G^\dagger\|\le e\sqrt k/(k-r)$.
--
--   **Formalization Note.** $\mu$ is a probability measure (`IsProbabilityMeasure`); the tail bound is stated as an inequality in `ENNReal` via `ENNReal.ofReal`; `t ^ (-m)` is the real power `Real.rpow`; nonnegativity is assumed only almost everywhere.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, "Finding structure with randomness", SIAM Review 53(2) (2011), proof of Proposition A.4 (integration of the tail bound); standard fact: E X = ∫_0^∞ P(X>t) dt for X ≥ 0.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem integral_le_of_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ) (hnn : 0 ≤ᵐ[μ] f)
    (C m : ℝ) (hC : 0 < C) (hm : 1 < m)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal (C * t ^ (-m))) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ C ^ (1 / m) * m / (m - 1) := by sorry

end GaussianMatrix
