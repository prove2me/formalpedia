-- Prove2me | Theorems.Thm_OnlineReviewPricing_candidate_path
-- name    : OnlineReviewPricing.candidate_path
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:28:23.739184+00:00
-- url     : https://prove2.me/theorems/6558131b-d2ae-4d65-b414-8770e49bafb1
-- title:
--   (13)–(14), p.14 — the candidate path is admissible with constant demand
-- statement:
--   Let $\gamma,T>0$ and let $z$ be a root of (14),
--
--   $$
--   z+\exp(z)=\mu-1+\frac{\mu_0-\mu}{\gamma\ell(z)T+1}.
--   $$
--
--   Let $n^*(t)=\ell(z)t$ and
--
--   $$
--   p^*(t)=1+\exp(z)+(\mu-\mu_0)\left(\frac{1}{\gamma n^*(T)+1}-\frac{1}{\gamma n^*(t)+1}\right).
--   $$
--
--   Then $(p^*,n^*)$ is admissible for the fluid problem, and along this path the demand is constant:
--
--   $$
--   \lambda\bigl(p^*(t),n^*(t)\bigr)=\ell(z)\qquad\text{for all }t\in[0,T].
--   $$
--
--   The price compensates exactly for the change in the posterior mean. This gives a family of candidate optima indexed by the roots of (14).
--
--   Differences from the source:
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (13)–(14), p.14

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsRootOf14
import Definitions.Def_OnlineReviewPricing_candidatePrice
import Definitions.Def_OnlineReviewPricing_candidatePath
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_demand

namespace OnlineReviewPricing

/-- For every root `z` of (14), the pair (13) is an admissible fluid path, and along it the demand
is the constant `ℓ(z)` on `[0, T]` (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (13)–(14), p.14). -/
theorem candidate_path (μ μ₀ γ T z : ℝ) (hγ : 0 < γ) (hT : 0 < T) (hz : IsRootOf14 μ μ₀ γ T z) :
    IsFluidPath μ μ₀ γ T (candidatePrice μ μ₀ γ T z) (candidatePath z) ∧
      ∀ t ∈ Set.Icc 0 T,
        demand μ μ₀ γ (candidatePrice μ μ₀ γ T z t) (candidatePath z t) = ell z := by sorry

end OnlineReviewPricing
