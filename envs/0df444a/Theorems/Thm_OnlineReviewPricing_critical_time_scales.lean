-- Prove2me | Theorems.Thm_OnlineReviewPricing_critical_time_scales
-- name    : OnlineReviewPricing.critical_time_scales
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:29:34.016061+00:00
-- url     : https://prove2.me/theorems/c557e786-70e6-449d-9cb8-064db97a342b
-- title:
--   Theorem 3, p.22 — critical time scales: the OFP ratio has a limit $\Delta(\kappa)$, equal to 1 exactly at $\kappa=0,\infty$ (corrected: $P$ contains $p_0,p_\infty$)
-- statement:
--   Consider the fluid problem (10) with quality-based reviews, and let $\mu_0\ne\mu$. Let $P\subseteq\mathbb R$ be a set of allowed fixed prices containing the static optima $p_0=\arg\max_p\{p\,\ell(\mu_0-p)\}$ and $p_\infty=\arg\max_p\{p\,\ell(\mu-p)\}$. Then there is a function $\Delta:[0,\infty]\to\mathbb R$ such that, for every $\kappa\in[0,\infty]$, as $\gamma T\to\kappa$ over all pairs $\gamma,T>0$,
--
--   $$
--   \frac{\bar J^{OFP}_T}{\bar J^*_T}\to\Delta(\kappa),
--   $$
--
--   and
--
--   1. $\Delta(0)=1$ (non-informative social learning);
--   2. $\Delta(\infty)=1$ (informative social learning);
--   3. $\Delta(\kappa)<1$ for $\kappa\in(0,\infty)$ (intermediate).
--
--   So a fixed price is asymptotically optimal when reviews are nearly uninformative over the horizon and when they reveal the quality almost at once, and it is strictly suboptimal exactly at the critical scale $\gamma T\asymp 1$.
--
--   **Formalization Note** $\kappa$ ranges over the extended nonnegative reals. The function $\Delta$ is fixed before the limit is taken, so it depends on $\kappa$ and on the fixed data $\mu,\mu_0,P$, and not on $(\gamma,T)$. Condition (15) is not assumed.
--
--   Differences from the source:
--   - correction: the fixed price ranges over [p̲, p̄], with no relation to the optimum → the fixed price ranges over a set P that contains the static optimum; reason: the printed statement is false: with µ = 1, µ₀ = 0, [p̲, p̄] = [10, 11] all assumptions hold, and as γT → 0 the ratio tends to about 0.0016
--   - generalization: OFP is an arg max over the interval [p̲, p̄] → fixedValue is a supremum over an arbitrary set P; reason: P = [p̲, p̄] with the hypothesis on P is the source's setting, and P = ℝ is the reading of §3.1, which drops the price constraint
--   - reading: 'as γT → κ'; the proof fixes T and varies γ → the limit is over every way that pairs (γ, T) with γ, T > 0 approach κ; reason: the theorem is stated in γT, and the stronger reading is true because J̄*/T and J̄^p/T depend only on γT
--   - encoding: κ ∈ [0, ∞] → κ : ℝ≥0∞, with the filter given by ENNReal.ofReal (γT); reason: the extended nonnegative reals are [0, ∞], and at finite κ this is ordinary convergence of γT
--   - encoding: J̄*_T = max over Ψ → sSup of the set of admissible revenues; reason: the set is nonempty and bounded above and the supremum is attained (Theorem 1), so the value is the same
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), Theorem 3, p.22

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsStaticOptimum
import Definitions.Def_OnlineReviewPricing_fixedValue
import Definitions.Def_OnlineReviewPricing_fluidValue

open Filter Topology
open scoped ENNReal

namespace OnlineReviewPricing

/-- Theorem 3 (Critical time scales: quality-based reviews). If `μ₀ ≠ μ`, then as `γ T → κ` the
ratio of the best fixed-price revenue to the optimal revenue of (10) tends to a constant `Δ(κ)`
depending only on `κ ∈ [0, ∞]`, with `Δ(0) = 1`, `Δ(∞) = 1` and `Δ(κ) < 1` for `κ ∈ (0, ∞)`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), Theorem 3, p.22).

**Formalization Note.** `κ` lives in `ℝ≥0∞`, the limit is over all pairs `γ, T > 0`, and `Δ` is
quantified before the limit, so it depends on `κ` and the fixed data `μ, μ₀, P` only. The set `P` of
allowed fixed prices contains the static optima `p₀` and `p_∞`: the page's arbitrary `[p̲, p̄]` makes
clauses (a), (b) false. `P = Set.univ`, and `P = Set.Icc p̲ p̄` when it holds both optima, are
instances. Condition (15) is not assumed. -/
theorem critical_time_scales (μ μ₀ : ℝ) (hμ : μ₀ ≠ μ) (P : Set ℝ)
    (hp₀ : ∀ p, IsStaticOptimum μ₀ p → p ∈ P) (hpInf : ∀ p, IsStaticOptimum μ p → p ∈ P) :
    ∃ Δ : ℝ≥0∞ → ℝ, Δ 0 = 1 ∧ Δ ⊤ = 1 ∧ (∀ κ, 0 < κ → κ < ⊤ → Δ κ < 1) ∧
      ∀ κ, Tendsto (fun x : ℝ × ℝ => fixedValue μ μ₀ P x.1 x.2 / fluidValue μ μ₀ x.1 x.2)
        (comap (fun x : ℝ × ℝ => ENNReal.ofReal (x.1 * x.2)) (𝓝 κ) ⊓ 𝓟 {x | 0 < x.1 ∧ 0 < x.2})
        (𝓝 (Δ κ)) := by sorry

end OnlineReviewPricing
