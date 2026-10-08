-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_mbLaw_eq_gaussian
-- name    : HighDimCLT.MultBoot.mbLaw_eq_gaussian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:38.15911+00:00
-- url     : https://prove2.me/theorems/0a495cec-e04f-414b-b7d0-feeb31a327bc
-- title:
--   App. E.2, p. 2342 — conditional on X₁ⁿ, S^{eX}_n is a centred Gaussian vector with covariance Σ̂
-- statement:
--   Fix $n\ge 4$, $p\in\mathbb N$ and a realization $x=(x_1,\dots,x_n)$ of the data in $\mathbb R^p$, with sample mean $\bar X=n^{-1}\sum_i x_i$. Let $e_1,\dots,e_n$ be i.i.d. standard normal random variables. Then the multiplier bootstrap sum
--   $$S_n^{eX}=\frac{1}{\sqrt n}\sum_{i=1}^n e_i(x_i-\bar X)$$
--   has law $N(0,\widehat\Sigma)$, where $\widehat\Sigma=n^{-1}\sum_{i=1}^n(x_i-\bar X)(x_i-\bar X)'$.
--
--   This is the fact that conditional on $X_1^n$ the bootstrap sum is a centred Gaussian vector with covariance $\widehat\Sigma$, which lets the proof of Theorem 4.1 compare two Gaussian laws.
--
--   **Formalization Note** The conditional law given $X_1^n=x$ is represented by the push-forward of the product measure $N(0,1)^{\otimes n}$ under $e\mapsto n^{-1/2}\sum_i e_i(x_i-\bar X)$; the conclusion is an equality of measures with Mathlib's `multivariateGaussian 0 Σ̂`.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2342, App. E.2, Proof of Theorem 4.1, "Note that conditional on X₁ⁿ"; cf. p. 2318, §4.1

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **App. E.2, p. 2342** (proof of Theorem 4.1): conditional on the data `X₁ⁿ = x`, the
multiplier-bootstrap sum `S^{eX}_n = n^{-1/2} ∑_i e_i (x_i − X̄)` with `e_i` i.i.d. `N(0, 1)` is a
centred Gaussian vector with covariance matrix `Σ̂ = n^{-1} ∑_i (x_i − X̄)(x_i − X̄)′`. -/
theorem mbLaw_eq_gaussian (n p : ℕ) (hn : 4 ≤ n) (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    mbLaw x = multivariateGaussian 0 (SigmaHat x) := by sorry

end HighDimCLT.MultBoot
