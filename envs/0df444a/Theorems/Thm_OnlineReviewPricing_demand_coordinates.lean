-- Prove2me | Theorems.Thm_OnlineReviewPricing_demand_coordinates
-- name    : OnlineReviewPricing.demand_coordinates
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:38.17835+00:00
-- url     : https://prove2.me/theorems/07143cd9-640e-4289-93c3-48cb04d8bf88
-- title:
--   (EC.14), p.ec8 — the fluid problem in demand coordinates (corrected: posterior mean in the price map)
-- statement:
--   Let $\gamma,T>0$. The fluid problem is equivalent to
--
--   $$
--   \max_{\lambda(\cdot)}\int_0^T p(\lambda(s),n(s))\,\lambda(s)\,ds\quad\text{subject to}\quad \dot n(t)=\lambda(t),\ t\in[0,T],
--   $$
--
--   with $p(\lambda,n)=\mu(n)+\log((1-\lambda)/\lambda)$. Precisely:
--
--   1. at every state $n$, the maps $p\mapsto\lambda(p,n)$ and $\lambda\mapsto p(\lambda,n)$ are mutually inverse between $\mathbb R$ and $(0,1)$;
--   2. if $(p,n)$ is admissible, then $\lambda(t)=\lambda(p(t),n(t))$ is an admissible demand path with state path $n$ and the same objective value;
--   3. if $(\lambda,n)$ is an admissible demand path, then $p(t)=p(\lambda(t),n(t))$ gives an admissible pair with state path $n$, demand $\lambda$ on $[0,T]$ and the same objective value.
--
--   The objective in demand coordinates is concave in the control, which is what makes the problem tractable.
--
--   Differences from the source:
--   - correction: p(λ, Φ) = µ + log((1 − λ)/λ), with the true mean µ → p(λ, n) = µ(n) + log((1 − λ)/λ), with the posterior mean; reason: the printed map is false: by (1)–(2) the demand at n = 0 is ℓ(µ₀ − p), and ℓ(µ₀ − p) ≠ ℓ(µ − p) for µ₀ ≠ µ, so the printed map does not invert the demand
--   - encoding: max over demand paths λ(·) → two-way correspondence between admissible paths, with equal objectives; reason: this is what 'equivalent' and 'the one-to-one mapping between the price and demand' mean, and it gives equal values and a bijection of solutions
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.14), p.ec8 (PDF 45), with the price map of p.ec7 (PDF 44)

import Mathlib
import Definitions.Def_OnlineReviewPricing_priceOfDemand
import Definitions.Def_OnlineReviewPricing_demand
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_IsDemandPath
import Definitions.Def_OnlineReviewPricing_fluidRevenue

namespace OnlineReviewPricing

/-- The fluid problem (10) is equivalent to the demand-coordinate problem (EC.14): the price–demand
map is a bijection between prices and demands in `(0, 1)` at each state; every admissible price path
maps to an admissible demand path with the same state path and the same objective; and every
admissible demand path comes from an admissible price path in the same way
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.14), p.ec8).

**Formalization Note.** The price map uses the posterior mean `μ(n)`, where the page has `μ`. -/
theorem demand_coordinates (μ μ₀ γ T : ℝ) (hγ : 0 < γ) (hT : 0 < T) :
    (∀ p n, priceOfDemand μ μ₀ γ (demand μ μ₀ γ p n) n = p) ∧
    (∀ l n, l ∈ Set.Ioo (0 : ℝ) 1 → demand μ μ₀ γ (priceOfDemand μ μ₀ γ l n) n = l) ∧
    (∀ p n, IsFluidPath μ μ₀ γ T p n →
      IsDemandPath T (fun t => demand μ μ₀ γ (p t) (n t)) n ∧
        fluidRevenue μ μ₀ γ T p n =
          ∫ s in (0 : ℝ)..T, priceOfDemand μ μ₀ γ (demand μ μ₀ γ (p s) (n s)) (n s) *
            demand μ μ₀ γ (p s) (n s)) ∧
    (∀ l n, IsDemandPath T l n →
      IsFluidPath μ μ₀ γ T (fun t => priceOfDemand μ μ₀ γ (l t) (n t)) n ∧
        (∀ t ∈ Set.Icc 0 T, demand μ μ₀ γ (priceOfDemand μ μ₀ γ (l t) (n t)) (n t) = l t) ∧
        fluidRevenue μ μ₀ γ T (fun t => priceOfDemand μ μ₀ γ (l t) (n t)) n =
          ∫ s in (0 : ℝ)..T, priceOfDemand μ μ₀ γ (l s) (n s) * l s) := by sorry

end OnlineReviewPricing
