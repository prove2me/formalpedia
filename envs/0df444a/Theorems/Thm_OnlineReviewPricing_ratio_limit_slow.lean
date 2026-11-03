-- Prove2me | Theorems.Thm_OnlineReviewPricing_ratio_limit_slow
-- name    : OnlineReviewPricing.ratio_limit_slow
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:29:11.534845+00:00
-- url     : https://prove2.me/theorems/a175f175-20fb-4287-be20-e30200160b7c
-- title:
--   Proof of Theorem 3, p.ec13 — OFP matches ODP as $\gamma\to 0$ (corrected: $P$ contains $p_0$)
-- statement:
--   Fix $T>0$, and let $P\subseteq\mathbb R$ be a set of allowed fixed prices containing the static optimum $p_0=\arg\max_p\{p\,\ell(\mu_0-p)\}$. Then
--
--   $$
--   1-\frac{\bar J^{OFP}_T}{\bar J^*_T}\to 0\qquad\text{as }\gamma\to 0^+ ,
--   $$
--
--   and every choice of optimal fixed prices $p^{OFP}$ in $P$ converges to $1+\exp(z_0^*)$, where $z_0^*+\exp(z_0^*)=\mu_0-1$.
--
--   When learning is slow, the optimal path is nearly constant, so a single price captures almost all of the optimal revenue.
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
import Definitions.Def_OnlineReviewPricing_IsOptimalFixedPrice
import Definitions.Def_OnlineReviewPricing_fixedValue
import Definitions.Def_OnlineReviewPricing_fluidValue

open Filter Topology

namespace OnlineReviewPricing

/-- For fixed `T > 0`, the ratio of the best fixed-price revenue to the optimal revenue tends to `1`
as `γ → 0⁺`, and any choice of optimal fixed prices tends to `1 + exp z₀`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), proof of Theorem 3, p.ec13).

**Formalization Note.** `P` must contain the static optimum `p₀`. The page's claim
`lim p^OFP = 1 + exp z₀*` assumes it. -/
theorem ratio_limit_slow (μ μ₀ T z₀ : ℝ) (P : Set ℝ) (hT : 0 < T)
    (hP : ∀ p, IsStaticOptimum μ₀ p → p ∈ P) (hz₀ : z₀ + Real.exp z₀ = μ₀ - 1) :
    Tendsto (fun γ => fixedValue μ μ₀ P γ T / fluidValue μ μ₀ γ T) (𝓝[>] 0) (𝓝 1) ∧
      ∀ c : ℝ → ℝ, (∀ᶠ γ in 𝓝[>] 0, IsOptimalFixedPrice μ μ₀ P γ T (c γ)) →
        Tendsto c (𝓝[>] 0) (𝓝 (1 + Real.exp z₀)) := by sorry

end OnlineReviewPricing
