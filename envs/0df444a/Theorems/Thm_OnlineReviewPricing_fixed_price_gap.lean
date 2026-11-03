-- Prove2me | Theorems.Thm_OnlineReviewPricing_fixed_price_gap
-- name    : OnlineReviewPricing.fixed_price_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:29:41.925782+00:00
-- url     : https://prove2.me/theorems/31b8b085-1a7b-4c12-9dd2-dec8b4e22610
-- title:
--   p.22 — fixed prices lose strictly to the dynamic optimum when $\mu_0\ne\mu$
-- statement:
--   Let $\gamma,T>0$ and $\mu_0\ne\mu$. Then the best fixed-price revenue over all real prices is strictly below the optimal revenue:
--
--   $$
--   \sup_{p\in\mathbb R}\bar J^{p}_T<\bar J^*_T .
--   $$
--
--   This is the loss that the paper describes for the intermediate regime: under a fixed price, demand must change as the belief moves, while the optimal path keeps demand constant.
--
--   Differences from the source:
--   - reading: 'a significant loss in revenue can be incurred under any fixed-price policy for the intermediate values of γT' → a strict gap between the supremum over all fixed prices and the optimum, for every γ, T > 0 with µ₀ ≠ µ; reason: the sentence is informal, and this is the precise claim that clause (c) of Theorem 3 needs at each finite γT
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
--   - encoding: J̄*_T = max over Ψ → sSup of the set of admissible revenues; reason: the set is nonempty and bounded above and the supremum is attained (Theorem 1), so the value is the same
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.22, discussion after Theorem 3

import Mathlib
import Definitions.Def_OnlineReviewPricing_fixedValue
import Definitions.Def_OnlineReviewPricing_fluidValue

namespace OnlineReviewPricing

/-- For every `γ, T > 0` with `μ₀ ≠ μ`, the supremum of fixed-price revenues over all real prices is
strictly below the optimal revenue (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), p.22). This is the content of clause (c) of Theorem 3
for finite `γ T`. -/
theorem fixed_price_gap (μ μ₀ γ T : ℝ) (hμ : μ₀ ≠ μ) (hγ : 0 < γ) (hT : 0 < T) :
    fixedValue μ μ₀ Set.univ γ T < fluidValue μ μ₀ γ T := by sorry

end OnlineReviewPricing
