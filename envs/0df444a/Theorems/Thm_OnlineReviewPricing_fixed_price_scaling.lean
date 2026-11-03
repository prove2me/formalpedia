-- Prove2me | Theorems.Thm_OnlineReviewPricing_fixed_price_scaling
-- name    : OnlineReviewPricing.fixed_price_scaling
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:29:15.446407+00:00
-- url     : https://prove2.me/theorems/4a385c5c-d0d2-41c5-8daf-9a3350d0f710
-- title:
--   (EC.28), p.ec14 — fixed-price revenue depends only on $\gamma T$
-- statement:
--   There is a function $\tilde n(p,\kappa)$, defined for $\kappa>0$, that solves the scaled sales equation and is continuous in $\kappa$, such that for every fixed price $p$ and all $\gamma,T>0$,
--
--   $$
--   \frac{\bar J^p_T}{T}=\frac{p\,n^p(T)}{T}=\frac{p\,\gamma n^p(T)}{\gamma T}=\frac{p\,\tilde n(p,\gamma T)}{\gamma T},\qquad \gamma n^p(T)=\tilde n(p,\gamma T).
--   $$
--
--   In particular, $\bar J^p_T/T\to p\,\tilde n(p,\kappa)/\kappa$ as $\gamma T\to\kappa$. For every set $P$ of allowed prices, the best fixed-price revenue per unit time is also a continuous function of $\gamma T$ alone.
--
--   Together with the corresponding statement for $\bar J^*_T/T$, this shows that the revenue ratio depends only on $\gamma T$.
--
--   Differences from the source:
--   - generalization: the limit J̄^π_T/T → pΔ′(κ)/κ as γT → κ, with Δ′ depending on κ → an exact formula in γT for all pairs, with nTilde(p, κ) continuous in κ, and the same for fixedValue/T over every P; reason: the exact formula with continuity implies the page's limit, and the page's closing 'they also hold for OFP' is the clause on fixedValue
--   - reading: Δ′(κ), written with κ only → nTilde p κ, depending on the price too; reason: the page's Δ′(κ) is ñ at price p, so it depends on p even though the notation hides it
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.28), p.ec14 (PDF 51)

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_fluidRevenue
import Definitions.Def_OnlineReviewPricing_fixedValue
import Definitions.Def_OnlineReviewPricing_scaledFixedPriceEquation

namespace OnlineReviewPricing

/-- There is a function `nTilde p κ`, solving the scaled equation and continuous in `κ > 0`, such
that for every fixed-price path `J̄ᵖ_T / T = p n(T) / T = p nTilde p (γ T) / (γ T)`. So fixed-price
revenue per unit time depends only on `(p, γ T)`, and the same holds for `fixedValue / T` for every
set `P` of allowed prices (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.28), p.ec14).

**Formalization Note.** The page's `Δ′(κ)` depends on the price too, so it is `nTilde p κ` here. The
limit of (EC.28) follows from the exact formula and the continuity of `nTilde p`. -/
theorem fixed_price_scaling (μ μ₀ : ℝ) :
    ∃ nTilde : ℝ → ℝ → ℝ,
      (∀ p κ, 0 < κ →
        0 ≤ nTilde p κ ∧ scaledFixedPriceEquation μ μ₀ κ p (nTilde p κ) = 0) ∧
      (∀ p, ContinuousOn (nTilde p) (Set.Ioi 0)) ∧
      (∀ p γ T n, 0 < γ → 0 < T → IsFluidPath μ μ₀ γ T (fun _ => p) n →
        fluidRevenue μ μ₀ γ T (fun _ => p) n / T = p * n T / T ∧
        γ * n T = nTilde p (γ * T) ∧
        fluidRevenue μ μ₀ γ T (fun _ => p) n / T = p * nTilde p (γ * T) / (γ * T)) ∧
      ∀ P : Set ℝ, ∃ F : ℝ → ℝ, ContinuousOn F (Set.Ioi 0) ∧
        ∀ γ T, 0 < γ → 0 < T → fixedValue μ μ₀ P γ T / T = F (γ * T) := by sorry

end OnlineReviewPricing
