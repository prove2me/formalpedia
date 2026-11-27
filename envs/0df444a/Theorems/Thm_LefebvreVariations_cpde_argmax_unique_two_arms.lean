-- Prove2me | Theorems.Thm_LefebvreVariations_cpde_argmax_unique_two_arms
-- name    : LefebvreVariations.cpde_argmax_unique_two_arms
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:28:51.273845+00:00
-- url     : https://prove2.me/theorems/7a7fd084-b8f8-47da-b71d-cc8d85f1fe4b
-- title:
--   Lefebvre's variations, No. 277 — on a theme by Chick, Gans and Yapar: the better of two arms with a Gaussian prior is almost surely unique
-- statement:
--   Let $\mu^0\in\mathbb R^2$ and let $\Sigma^0$ be a positive definite real $2\times2$ matrix. If $\theta=(\theta_0,\theta_1)$ is a random vector with the Gaussian law $N(\mu^0,\Sigma^0)$ on $\mathbb R^2$, then almost surely there is an index $i\in\{0,1\}$ with $\theta_j<\theta_i$ for the other index $j$; in other words $\Pr\{\theta_0=\theta_1\}=0$.
--
--   For $M\ge2$ arms with a Gaussian prior on the arm means, the best arm is almost surely unique; this is the remark that the proof of the consistency theorem for the cPDE allocation policy uses. Here the first size $M=2$ is taken, where the claim is that $\theta_0-\theta_1$, a real Gaussian with positive variance $(1,-1)\Sigma^0(1,-1)^{\top}$, has no atom at $0$.
--
--   **Formalization Note** The law hypothesis is `P.map θ = multivariateGaussian (WithLp.toLp 2 mu0) Sig0`, with `θ` valued in `EuclideanSpace ℝ (Fin 2)`, exactly as in the parent with `M = 2`; measurability of `θ` is forced by the law hypothesis, since the push-forward by a non-measurable map is zero. The conclusion is the parent's: `∀ᵐ ω ∂P, ∃ i, ∀ j, j ≠ i → θ ω j < θ ω i`.
--
--   **Why this is a variation.** A variation on the open platform problem CPDETrial.argmax_unique (the best arm is almost surely unique when the arm means have a positive definite Gaussian law, for every number of arms M >= 2), taken at the first size M = 2. It is a special case of the parent with the same hypotheses and conclusion and M fixed to 2.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Chick, Gans and Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758, proof of Theorem 1 (the remark that the arg max is uniquely defined with probability 1, as recorded by the platform's parent statement; not re-read). For M = 2 the claim is elementary: theta_0 - theta_1 is Gaussian with variance (1,-1) Sigma (1,-1)^T > 0, so it has no atom at 0.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory

/-- The best of two arms is almost surely unique when the arm means have a nondegenerate bivariate Gaussian law.
If `θ ∼ N(µ⁰, Σ⁰)` on `ℝ²` with `Σ⁰` positive definite, then almost surely one coordinate is strictly larger than the other, since `θ₀ - θ₁` is a nondegenerate real Gaussian and has no atom at `0`.
Source: the remark in the proof of Theorem 1 of Chick, Gans, Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions*, SSRN 3184758, as recorded by the platform. -/
theorem cpde_argmax_unique_two_arms {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (mu0 : Fin 2 → ℝ)
    (Sig0 : Matrix (Fin 2) (Fin 2) ℝ) (hSig0 : Sig0.PosDef)
    (θ : Ω → EuclideanSpace ℝ (Fin 2))
    (hlaw : P.map θ = multivariateGaussian (WithLp.toLp 2 mu0) Sig0) :
    ∀ᵐ ω ∂P, ∃ i, ∀ j, j ≠ i → θ ω j < θ ω i := by
  sorry

end LefebvreVariations
