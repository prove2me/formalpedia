-- Prove2me | Theorems.Thm_OnlineReviewPricing_fixed_price_sales
-- name    : OnlineReviewPricing.fixed_price_sales
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:23.896034+00:00
-- url     : https://prove2.me/theorems/ee4cf3c8-5636-444e-b85e-7690b238de36
-- title:
--   (EC.27) ff., pp.ec13–14 — total sales at a fixed price solve an integral equation
-- statement:
--   Let $\gamma,T>0$ and fix a price $p$. The fluid path $n^p$ under the constant price $p$ exists and is unique on $[0,T]$. Its total sales $n=n^p(T)$ are the unique nonnegative solution of
--
--   $$
--   n-T+\exp(p-\mu)\int_0^n\exp\left(\frac{\mu-\mu_0}{1+\gamma x}\right)dx=0 ,
--   $$
--
--   and $\tilde n=\gamma n^p(T)$ is the unique nonnegative solution of
--
--   $$
--   \tilde n-\kappa+\exp(p-\mu)\int_0^{\tilde n}\exp\left(\frac{\mu-\mu_0}{1+x}\right)dx=0,\qquad \kappa=\gamma T .
--   $$
--
--   The scaled equation does not involve $\gamma$ and $T$ separately.
--
--   Differences from the source:
--   - generalization: ñ^π(T) 'approaches the solution ñ' of the scaled equation as γT → κ → γ n(T) solves the scaled equation exactly, at κ = γT; reason: the substitution y = γx gives an exact identity for every pair, which contains the page's limit together with the continuity of fixed_price_scaling
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.27) and the two displays after it, pp.ec13–ec14 (PDF 50–51)

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_fixedPriceEquation
import Definitions.Def_OnlineReviewPricing_scaledFixedPriceEquation

namespace OnlineReviewPricing

/-- For a fixed price `c`, the fluid path exists and is unique on `[0, T]`, and its total sales
`n(T)` are the unique nonnegative solution of the equation after (EC.27). Moreover `γ n(T)` is the
unique nonnegative solution of the scaled equation at `κ = γ T`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.27) ff., pp.ec13–ec14). -/
theorem fixed_price_sales (μ μ₀ γ T c : ℝ) (hγ : 0 < γ) (hT : 0 < T) :
    (∃ n, IsFluidPath μ μ₀ γ T (fun _ => c) n) ∧
    (∀ n n', IsFluidPath μ μ₀ γ T (fun _ => c) n → IsFluidPath μ μ₀ γ T (fun _ => c) n' →
      ∀ t ∈ Set.Icc 0 T, n t = n' t) ∧
    ∀ n, IsFluidPath μ μ₀ γ T (fun _ => c) n →
      0 ≤ n T ∧ fixedPriceEquation μ μ₀ γ T c (n T) = 0 ∧
      (∀ m, 0 ≤ m → fixedPriceEquation μ μ₀ γ T c m = 0 → m = n T) ∧
      scaledFixedPriceEquation μ μ₀ (γ * T) c (γ * n T) = 0 ∧
      (∀ x, 0 ≤ x → scaledFixedPriceEquation μ μ₀ (γ * T) c x = 0 → x = γ * n T) := by sorry

end OnlineReviewPricing
