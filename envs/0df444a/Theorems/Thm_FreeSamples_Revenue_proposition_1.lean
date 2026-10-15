-- Prove2me | Theorems.Thm_FreeSamples_Revenue_proposition_1
-- name    : FreeSamples.Revenue.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:48.597272+00:00
-- url     : https://prove2.me/theorems/d94eb01c-08b8-4861-8005-8b612b3c8f70
-- title:
--   Proposition 1, p. 13 — the Buyer's and the Seller's posteriors on θ given the data path are Gaussian with the stated means and variances
-- statement:
--   Fix the parameters $\theta_0,\mu_b$, $\sigma_0^2>0$, $\sigma_b^2\ge 0$ and $\sigma^2>0$, and put $\sigma_s^2=\sigma_0^2+\sigma_b^2$. Let $Y_t=\theta t+\sigma B_t$, with $\mathcal F_t$ its natural filtration.
--
--   1. Under the Buyer's model, with $\theta\sim\mathcal N(\theta_0,\sigma_0^2)$ independent of the Brownian motion $B$, the conditional law of $\theta$ given $\mathcal F_t$ is $\mathcal N(\theta_t,\sigma_t^2)$, where
--   $$\theta_t=\frac{\sigma_t^2}{\sigma_0^2}\theta_0+\frac{\sigma_t^2}{\sigma^2}Y_t,\qquad \sigma_t^2=\frac{\sigma_0^2\sigma^2}{\sigma_0^2t+\sigma^2}.$$
--   2. Under the Seller's model, with $\theta\sim\mathcal N(\theta_0+\mu_b,\sigma_s^2)$, the conditional law of $\theta$ given $\mathcal F_t$ is $\mathcal N(\tilde\theta_t,\tilde\sigma_t^2)$, where
--   $$\tilde\theta_t=\frac{\tilde\sigma_t^2}{\sigma_s^2}(\theta_0+\mu_b)+\frac{\tilde\sigma_t^2}{\sigma^2}Y_t,\qquad \tilde\sigma_t^2=\frac{\sigma_s^2\sigma^2}{\sigma_s^2t+\sigma^2}.$$
--   3. For every $t\ge 0$ and every value of $Y_t$,
--   $$\tilde\theta_t=\frac{\tilde\sigma_t^2}{\sigma_s^2}(\theta_0+\mu_b)+\frac{\tilde\sigma_t^2}{\sigma_t^2}\theta_t-\frac{\tilde\sigma_t^2}{\sigma_0^2}\theta_0.$$
--
--   Here "the conditional law is $\mathcal N(m,v)$" means that for every bounded measurable $\varphi$, almost surely $\mathbb E[\varphi(\theta)\mid\mathcal F_t]=\int\varphi\,d\mathcal N(m,v)$. The proposition gives the closed-form learning dynamics that every later statement of the paper is built on. The posterior depends on the data path only through $Y_t$.
--
--   **Formalization Note.** Conditioning is on the whole path $(Y_s)_{s\le t}$, not only on $Y_t$. Parts 1 and 2 are each stated for every probability space carrying the model, in a fixed universe.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 13, Proposition 1

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

universe u

theorem proposition_1 (p : Params) :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (hM : IsModel P p.θ₀ p.σ₀sq θ B) (t : ℝ≥0) (φ : ℝ → ℝ), Measurable φ →
      (∃ C, ∀ x, |φ x| ≤ C) →
      P[φ ∘ θ | dataFiltration p.σsq θ B hM.meas_θ hM.meas_B t] =ᵐ[P]
        fun ω => ∫ x, φ x ∂N (p.buyerMean t (Y p.σsq θ B t ω)) (p.buyerVar t)) ∧
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (hM : IsModel P (p.θ₀ + p.μb) p.σssq θ B) (t : ℝ≥0) (φ : ℝ → ℝ), Measurable φ →
      (∃ C, ∀ x, |φ x| ≤ C) →
      P[φ ∘ θ | dataFiltration p.σsq θ B hM.meas_θ hM.meas_B t] =ᵐ[P]
        fun ω => ∫ x, φ x ∂N (p.sellerMean t (Y p.σsq θ B t ω)) (p.sellerVar t)) ∧
    (∀ (t : ℝ≥0) (y : ℝ),
      p.sellerMean t y = p.sellerVar t / p.σssq * (p.θ₀ + p.μb)
        + p.sellerVar t / p.buyerVar t * p.buyerMean t y - p.sellerVar t / p.σ₀sq * p.θ₀) := by sorry

end FreeSamples.Revenue
