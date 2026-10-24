-- Prove2me | Theorems.Thm_FreeSamples_Revenue_theorem_1a
-- name    : FreeSamples.Revenue.theorem_1a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:55.691701+00:00
-- url     : https://prove2.me/theorems/796421ea-be79-4cc0-a922-bfe949d9efec
-- title:
--   Theorem 1(a), p. 17 — if the initial Seller-side drift (4) of the Bayes risk is positive, some free-sample policy earns strictly more than selling in one round
-- statement:
--   Let $u$ satisfy HasMax and Assumption 1, and let the Bayes risk $BR$ satisfy the growth hypothesis on variances in $(0,\sigma_0^2]$. Suppose
--   $$\tfrac12 BR_{\theta\theta}(\theta_0,\sigma_0^2)-BR_{\sigma^2}(\theta_0,\sigma_0^2)+\frac{\mu_b}{\sigma_0^2}BR_\theta(\theta_0,\sigma_0^2)>0. \tag{4}$$
--   Then, under the Seller's model ($\theta\sim\mathcal N(\theta_0+\mu_b,\sigma_s^2)$, data $Y_t=\theta t+\sigma B_t$ with $B$ a Brownian motion independent of $\theta$), there is a free-sample policy, that is, a bounded stopping time $T$ of the data filtration, whose revenue $BR(\theta_T,\sigma_T^2)$ is integrable and satisfies
--   $$\mathbb E^S_0\big[BR(\theta_T,\sigma_T^2)\big]>BR(\theta_0,\sigma_0^2).$$
--
--   The right-hand side is the revenue of selling in one round (the policy $T=0$, priced by Lemma 3). So the optimal free-sample policy earns strictly more than any one-round policy. When the Seller believes the Buyer's prior to be biased enough, giving data away for free before selling pays.
--
--   **Formalization Note.** "The optimal free-sample policy is strictly better" is rendered as the existence of one policy that is strictly better; no supremum over policies is formed. Policies are bounded stopping times of the natural filtration of $Y$; the paper's own construction stops by a large deterministic time $M$. Expectations are under the Seller's measure, as the theorem states. HasMax, Assumption 1 read as $C^2$ and the growth hypothesis are disclosed pins that keep every expectation and maximum a genuine one.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 17, Theorem 1(a), condition (4); p. 18 (expectation under E^S_0); proof pp. 30–31

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

theorem theorem_1a (p : Params) (u : ℝ → ℝ → ℝ) (hu : HasMax u) (hA : Assumption1 u)
    (hG : GrowthPin (BR u) p.σ₀sq)
    (h4 : 0 < (1 / 2) * dθθ (BR u) p.θ₀ p.σ₀sq - dv (BR u) p.θ₀ p.σ₀sq
      + p.μb / p.σ₀sq * dθ (BR u) p.θ₀ p.σ₀sq)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : IsModel P (p.θ₀ + p.μb) p.σssq θ B) :
    ∃ T : Ω → ℝ≥0, IsFreeSamplePolicy (dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) T ∧
      Integrable (revenue p u θ B T) P ∧
      BR u p.θ₀ p.σ₀sq < ∫ ω, revenue p u θ B T ω ∂P := by sorry

end FreeSamples.Revenue
