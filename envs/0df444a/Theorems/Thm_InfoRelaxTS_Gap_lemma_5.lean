-- Prove2me | Theorems.Thm_InfoRelaxTS_Gap_lemma_5
-- name    : InfoRelaxTS.Gap.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:21.611835+00:00
-- url     : https://prove2.me/theorems/77fb6d1d-2893-4931-bcf6-4d5d5ec85d2b
-- title:
--   Lemma 5, p. 67 — μ_a is √(L/ν)-sub-Gaussian and μ̂_{a,n} is √(Ln/(ν(ν+n)))-sub-Gaussian
-- statement:
--   Consider the setting of Theorem 3: a normalized natural-exponential-family bandit whose log-partition functions are $L$-smooth, and prior beliefs $y_b=(\xi_b,\nu)$ with a common $\nu>0$ that give proper priors, under which the rewards are integrable (3). Fix an arm $a$ and $n\ge0$. Then the prior predictive mean is
--   $$\bar\mu_a=\mathbb E_{(\xi_a,\nu)}[\mu_a]=\frac{\xi_a}{\nu},$$
--   the conditional mean reward $\mu_a(\theta_a)$, $\theta_a\sim\mathcal P_a(\xi_a,\nu)$, is $\sqrt{L/\nu}$-sub-Gaussian,
--   $$\mathbb E_{(\xi_a,\nu)}\big[\exp(\lambda(\mu_a-\bar\mu_a))\big]\le\exp\Big(\frac{L\lambda^2}{2\nu}\Big)\qquad(\lambda\in\mathbb R),$$
--   and the posterior predictive mean $\hat\mu_{a,n}$ under the outcome law $\mathcal I(y)$ is $\sqrt{Ln/(\nu(\nu+n))}$-sub-Gaussian,
--   $$\mathbb E_{(\xi_a,\nu)}\big[\exp(\lambda(\hat\mu_{a,n}-\bar\mu_a))\big]\le\exp\Big(\frac{\lambda^2}{2}\cdot\frac{Ln}{\nu(\nu+n)}\Big)\qquad(\lambda\in\mathbb R).$$
--
--   These concentration bounds are what turn the instantaneous suboptimalities of Lemma 3 into the $\sqrt{L}$-scaled terms of Theorem 3.
--
--   **Formalization Note** Sub-Gaussianity is Mathlib's `HasSubgaussianMGF` with variance proxy $L/\nu$, resp. $Ln/(\nu(\nu+n))$ (Definition 3 with the $\sigma^2$ reading), which includes integrability of every $e^{\lambda(\cdot)}$. The proxies are written with `Real.toNNReal`; they are nonnegative because $A_a$ is convex, so $L\ge0$. $\bar\mu_a$ and $\hat\mu_{a,n}$ are the integral definitions of the setting, so $\bar\mu_a=\xi_a/\nu$ is a conclusion here, not an assumption. The hypotheses are stated for every arm because $\mathcal I(y)$ is the product over all arms.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 67, Lemma 5, (214)–(215)

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting

open MeasureTheory ProbabilityTheory

namespace InfoRelaxTS.Gap

theorem lemma_5 {K : ℕ} (M : NEFModel K) (L ν : ℝ) (ξ : Fin K → ℝ)
    (hnorm : IsNormalized M) (hsmooth : IsLSmooth M L)
    (hprior : ∀ b, IsProperPrior M b (ξ b, ν))
    (hint : ∀ b, Integrable (fun r : ℝ => r) (predLaw M b (ξ b, ν)))
    (a : Fin K) (n : ℕ) :
    muBar M a (ξ a, ν) = ξ a / ν ∧
    HasSubgaussianMGF (fun θ => mu M a θ - muBar M a (ξ a, ν)) (Real.toNNReal (L / ν))
      (prior M a (ξ a, ν)) ∧
    HasSubgaussianMGF (fun ω => muHat M (fun b => (ξ b, ν)) a n ω - muBar M a (ξ a, ν))
      (Real.toNNReal (L * n / (ν * (ν + n)))) (I M (fun b => (ξ b, ν))) := by sorry

end InfoRelaxTS.Gap
