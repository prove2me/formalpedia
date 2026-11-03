-- Prove2me | Theorems.Thm_OnlineReviewPricing_theorem_1
-- name    : OnlineReviewPricing.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:29:34.978291+00:00
-- url     : https://prove2.me/theorems/91ad21a9-de2a-4099-98ba-45140329f6dd
-- title:
--   Theorem 1, p.14 — an optimal path exists, and under (15) it is the path (13)
-- statement:
--   Let $\gamma,T>0$. An optimal solution to the fluid problem (10) exists. If further
--
--   $$
--   \frac{\gamma T(\mu-\mu_0)}{4(1+\gamma T)}<1, \tag{15}
--   $$
--
--   then equation (14) has a unique root $z^*$, the pair $(p^*,n^*)$ of (13) at $z^*$ is optimal, and it is the unique optimal solution: every optimal pair $(p,n)$ has $n=n^*$ on $[0,T]$ and $p=p^*$ on $[0,T]$ off a finite set of times.
--
--   This is the closed-form solution of the fluid problem, and the rest of the analysis of quality-based reviews rests on it.
--
--   Differences from the source:
--   - reading: the price in (13) 'is the unique optimal solution' → every optimal price path equals p* off a finite set of times; reason: elements of Ψ are functions on [0, T], and changing p* at one point gives another element of Ψ with the same path and revenue, so pointwise uniqueness is false; the set-of-times reading is the only true one
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), Theorem 1, p.14

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsOptimalPath
import Definitions.Def_OnlineReviewPricing_IsRootOf14
import Definitions.Def_OnlineReviewPricing_candidatePrice
import Definitions.Def_OnlineReviewPricing_candidatePath

namespace OnlineReviewPricing

/-- Theorem 1 (Optimal solution to the fluid problem). An optimal solution to (10) exists. If
condition (15) holds, then (14) has a unique root `z`, the path (13) at `z` is optimal, and every
optimal pair has the state path of (13) on `[0, T]` and the price path of (13) off a finite set
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), Theorem 1, p.14).

**Formalization Note.** Changing a price path at finitely many times gives another element of `Ψ`
with the same state path and revenue, so uniqueness can hold only up to a finite set of times. -/
theorem theorem_1 (μ μ₀ γ T : ℝ) (hγ : 0 < γ) (hT : 0 < T) :
    (∃ p n, IsOptimalPath μ μ₀ γ T p n) ∧
      (γ * T * (μ - μ₀) / (4 * (1 + γ * T)) < 1 →
        ∃ z, IsRootOf14 μ μ₀ γ T z ∧ (∀ z', IsRootOf14 μ μ₀ γ T z' → z' = z) ∧
          IsOptimalPath μ μ₀ γ T (candidatePrice μ μ₀ γ T z) (candidatePath z) ∧
          ∀ p n, IsOptimalPath μ μ₀ γ T p n →
            (∀ t ∈ Set.Icc 0 T, n t = candidatePath z t) ∧
            ∃ A : Finset ℝ, ∀ t ∈ Set.Icc 0 T, t ∉ A → p t = candidatePrice μ μ₀ γ T z t) := by sorry

end OnlineReviewPricing
