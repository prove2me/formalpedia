-- Prove2me | Theorems.Thm_FreeSamples_Revenue_lemma_4b
-- name    : FreeSamples.Revenue.lemma_4b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:56.751053+00:00
-- url     : https://prove2.me/theorems/630ed2dd-7da4-43fb-8951-e62f6c28e390
-- title:
--   Lemma 4(b), p. 17 — from the Seller's perspective the Bayes risk drifts at rate (½BR_θθ − BR_σ² + (g_t/σ_t²)BR_θ)σ_t⁴/σ²
-- statement:
--   Let $u$ satisfy HasMax and Assumption 1, and let $BR$ satisfy the growth hypothesis on variances in $(0,\sigma_0^2]$. Under the Seller's model, $\theta\sim\mathcal N(\theta_0+\mu_b,\sigma_s^2)$ independent of $B$, let $\theta_h,\sigma_h^2$ be the Buyer's posterior after $h$ samples. Then $h\mapsto\mathbb E^S[BR(\theta_h,\sigma_h^2)]$ has right derivative at $h=0$
--   $$\Big(\tfrac12 BR_{\theta\theta}(\theta_0,\sigma_0^2)-BR_{\sigma^2}(\theta_0,\sigma_0^2)+\frac{\mu_b}{\sigma_0^2}BR_\theta(\theta_0,\sigma_0^2)\Big)\frac{\sigma_0^4}{\sigma^2}.$$
--
--   This is Lemma 4(b) at the initial state, where $g_0=\mu_b$. The first two terms are the holdup cost, the drop in the Bayes risk caused by learning. The third is the persuasion benefit, the Seller's expectation that the Buyer's belief moves toward hers. With condition (4) it yields Theorem 1(a).
--
--   **Formalization Note.** The page prints the factor $\sigma_t^4/\sigma_0^2$. Lemma 1 gives $\sigma_t^4/\sigma^2$, and the statement uses $\sigma^2$; the sign, and therefore Theorem 1, is unaffected. The paper's "at any $t\ge0$" in $dt$-notation is posed at time $0$ for arbitrary parameters. The growth hypothesis is a disclosed integrability pin.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 17, Lemma 4(b); proof p. 30

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

theorem lemma_4b (p : Params) (u : ℝ → ℝ → ℝ) (hu : HasMax u) (hA : Assumption1 u)
    (hG : GrowthPin (BR u) p.σ₀sq)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : IsModel P (p.θ₀ + p.μb) p.σssq θ B) :
    HasDerivWithinAt
      (fun h : ℝ => ∫ ω, BR u (p.buyerMean h (Y p.σsq θ B h.toNNReal ω)) (p.buyerVar h) ∂P)
      (drift (BR u) p.θ₀ p.σ₀sq p.μb * p.σ₀sq ^ 2 / p.σsq)
      (Set.Ici 0) 0 := by sorry

end FreeSamples.Revenue
