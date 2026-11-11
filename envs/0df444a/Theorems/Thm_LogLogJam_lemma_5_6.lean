-- Prove2me | Theorems.Thm_LogLogJam_lemma_5_6
-- name    : LogLogJam.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:01.171205+00:00
-- url     : https://prove2.me/theorems/e80c33c7-84d8-41df-8a90-e3d260852cda
-- title:
--   Lemma 5.6 — chain rule for Fisher information
-- statement:
--   Let $(X,\mu)$, $(Y,\nu)$ be measure spaces and let the joint density of $(X,Y)$ under the parameter $\theta$ be $q_\theta(x,y)=a_\theta(x)\,b_\theta(y\mid x)$, with $a_\theta$ the marginal density of $X$ and $b_\theta(\cdot\mid x)$ the conditional density of $Y$ given $X=x$. Assume positive densities, differentiable in $\theta$, measurable with measurable $\theta$-derivatives, and $\int\partial_\theta b_\theta(y\mid x)\,d\nu(y)=0$ with $\partial_\theta b_\theta(\cdot\mid x)$ integrable. Then
--
--   $$
--   J_{X,Y}(\theta)=J_X(\theta)+\mathbb E_{X\sim a_\theta}\big[J_{Y\mid X}(\theta)\big],\qquad J_{Y\mid X}(\theta)=\mathbb E_{Y\sim b_\theta(\cdot\mid X)}\big[(\partial_\theta\log b_\theta(Y\mid X))^2\big].
--   $$
--
--   This standard identity drives both Corollary 5.7 and Lemma 5.10.
--
--   Differences from the source:
--
--   - reading: “for any family of joint distributions $q_\theta(X,Y)$” → densities $a_\theta(x)b_\theta(y\mid x)$ w.r.t. $\mu\otimes\nu$; positive, differentiable at $\theta$, measurable with measurable derivatives; $\int\partial_\theta b\,d\nu=0$ with $\partial_\theta b$ integrable; reason: the Fisher informations in the statement need densities differentiable in $\theta$; the zero-mean conditional score (differentiation under the integral sign) is what makes the cross term vanish, and the source's “distributions” are understood with this regularity
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 5.6, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_LogLogJam_fisherInfo

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- **Lemma 5.6 (chain rule for Fisher information)** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 5.6, p.25): "For any family of
joint distributions q_θ(X, Y), we have J_{X,Y}(θ) = J_X(θ) + E_{X∼q_θ(X)}[J_{Y|X}(θ)], where
J_{Y|X}(θ) = E_{Y∼q_θ(Y|X)}[(∂_θ log q_θ(Y|X))²]."

The joint density is `q_θ(x, y) = a θ x · b θ x y` with respect to `μ ⊗ ν`, where `a θ` is the
marginal density of `X` and `b θ x` the conditional density of `Y` given `X = x`.

**Formalization Note** The regularity implicit in "family of joint distributions" with Fisher
informations is stated: positive densities, differentiable in `θ`, measurable (with measurable
`θ`-derivatives), and differentiation under the integral sign for the conditional density
(`∫ ∂_θ b dν = 0`, with `∂_θ b` integrable). Values in `[0, ∞]`. -/
theorem lemma_5_6 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) (a : ℝ → X → ℝ) (b : ℝ → X → Y → ℝ) (θ : ℝ)
    (ha : ∀ θ x, 0 < a θ x) (hb : ∀ θ x y, 0 < b θ x y)
    (hda : ∀ x, DifferentiableAt ℝ (fun θ' => a θ' x) θ)
    (hdb : ∀ x y, DifferentiableAt ℝ (fun θ' => b θ' x y) θ)
    (hma : Measurable (a θ)) (hmb : Measurable (Function.uncurry (b θ)))
    (hmda : Measurable (fun x => deriv (fun θ' => a θ' x) θ))
    (hmdb : Measurable (Function.uncurry fun x y => deriv (fun θ' => b θ' x y) θ))
    (hanorm : ∫⁻ x, ENNReal.ofReal (a θ x) ∂μ = 1)
    (hbnorm : ∀ x, ∫⁻ y, ENNReal.ofReal (b θ x y) ∂ν = 1)
    (hint : ∀ x, Integrable (fun y => deriv (fun θ' => b θ' x y) θ) ν)
    (hzero : ∀ x, ∫ y, deriv (fun θ' => b θ' x y) θ ∂ν = 0) :
    fisherInfo (μ.prod ν) (fun θ' p => a θ' p.1 * b θ' p.1 p.2) θ =
      fisherInfo μ a θ + ∫⁻ x, ENNReal.ofReal (a θ x) * fisherInfo ν (fun θ' y => b θ' x y) θ ∂μ := by sorry

end LogLogJam
