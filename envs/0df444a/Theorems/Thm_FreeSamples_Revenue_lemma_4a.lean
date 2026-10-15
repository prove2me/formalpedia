-- Prove2me | Theorems.Thm_FreeSamples_Revenue_lemma_4a
-- name    : FreeSamples.Revenue.lemma_4a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:47.525378+00:00
-- url     : https://prove2.me/theorems/16e71d16-2e7d-4509-bd20-d06ec9b45574
-- title:
--   Lemma 4(a), p. 17 — from the Buyer's perspective the Bayes risk drifts at rate (½BR_θθ − BR_σ²)σ_t⁴/σ²
-- statement:
--   Let $u$ satisfy HasMax and Assumption 1, and let $BR$ satisfy the growth hypothesis on variances in $(0,\sigma_0^2]$. Under the Buyer's model, $\theta\sim\mathcal N(\theta_0,\sigma_0^2)$ independent of $B$, let $\theta_h,\sigma_h^2$ be the Buyer's posterior after $h$ samples. Then $h\mapsto\mathbb E^B[BR(\theta_h,\sigma_h^2)]$ has right derivative at $h=0$
--   $$\Big(\tfrac12 BR_{\theta\theta}(\theta_0,\sigma_0^2)-BR_{\sigma^2}(\theta_0,\sigma_0^2)\Big)\frac{\sigma_0^4}{\sigma^2}.$$
--
--   This is Lemma 4(a) at the initial state. For the Buyer the Bayes risk drifts by the holdup cost alone, which by Lemma 2 is non-positive.
--
--   **Formalization Note.** The page subtracts $BR(\theta_{t+dt},\sigma^2_{t+dt})$ on the left and prints the factor $\sigma_t^4/\sigma_0^2$. The proof (p. 30) and part (b) subtract $BR(\theta_t,\sigma_t^2)$, and Lemma 1 gives $\sigma_t^4/\sigma^2$; the statement uses both corrections. It is posed at time $0$ for arbitrary parameters.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 17, Lemma 4(a); proof p. 30

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

theorem lemma_4a (p : Params) (u : ℝ → ℝ → ℝ) (hu : HasMax u) (hA : Assumption1 u)
    (hG : GrowthPin (BR u) p.σ₀sq)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : IsModel P p.θ₀ p.σ₀sq θ B) :
    HasDerivWithinAt
      (fun h : ℝ => ∫ ω, BR u (p.buyerMean h (Y p.σsq θ B h.toNNReal ω)) (p.buyerVar h) ∂P)
      (((1 / 2) * dθθ (BR u) p.θ₀ p.σ₀sq - dv (BR u) p.θ₀ p.σ₀sq) * p.σ₀sq ^ 2 / p.σsq)
      (Set.Ici 0) 0 := by sorry

end FreeSamples.Revenue
