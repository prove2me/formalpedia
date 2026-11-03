-- Prove2me | Theorems.Thm_OnlineReviewPricing_ratio_limit_fast
-- name    : OnlineReviewPricing.ratio_limit_fast
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:29:25.690208+00:00
-- url     : https://prove2.me/theorems/6dd20ffc-5d4e-4fde-aa18-5adad8b15efb
-- title:
--   Proof of Theorem 3, p.ec13 — OFP matches ODP as $\gamma\to\infty$ (corrected: $P$ contains $p_\infty$)
-- statement:
--   Fix $T>0$, and let $P\subseteq\mathbb R$ be a set of allowed fixed prices containing the static optimum $p_\infty=\arg\max_p\{p\,\ell(\mu-p)\}$. Then
--
--   $$
--   1-\frac{\bar J^{OFP}_T}{\bar J^*_T}\to 0\qquad\text{as }\gamma\to\infty .
--   $$
--
--   When learning is fast, customers recover the true quality early in the horizon, and the optimal revenue is nearly that of the single price $p_\infty$.
--
--   Differences from the source:
--   - correction: the fixed price ranges over [p̲, p̄], with no relation to the optimum → the fixed price ranges over a set P that contains the static optimum; reason: the printed statement is false: with µ = 1, µ₀ = 0, [p̲, p̄] = [10, 11] all assumptions hold, and as γT → 0 the ratio tends to about 0.0016
--   - generalization: OFP is an arg max over the interval [p̲, p̄] → fixedValue is a supremum over an arbitrary set P; reason: P = [p̲, p̄] with the hypothesis on P is the source's setting, and P = ℝ is the reading of §3.1, which drops the price constraint
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
--   - encoding: J̄*_T = max over Ψ → sSup of the set of admissible revenues; reason: the set is nonempty and bounded above and the supremum is attained (Theorem 1), so the value is the same
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), proof of Theorem 3, p.ec13 (PDF 50)

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsStaticOptimum
import Definitions.Def_OnlineReviewPricing_fixedValue
import Definitions.Def_OnlineReviewPricing_fluidValue

open Filter Topology

namespace OnlineReviewPricing

/-- For fixed `T > 0`, the ratio of the best fixed-price revenue to the optimal revenue tends to `1`
as `γ → ∞` (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), proof of Theorem 3, p.ec13).

**Formalization Note.** `P` must contain the static optimum `p_∞`. This is a statement about values:
the price (13) converges only for `t > 0`, since `p*(0) = μ₀ - z` while `p*(t)` tends to the limit
`p_∞` for `t > 0`. -/
theorem ratio_limit_fast (μ μ₀ T : ℝ) (P : Set ℝ) (hT : 0 < T)
    (hP : ∀ p, IsStaticOptimum μ p → p ∈ P) :
    Tendsto (fun γ => fixedValue μ μ₀ P γ T / fluidValue μ μ₀ γ T) atTop (𝓝 1) := by sorry

end OnlineReviewPricing
