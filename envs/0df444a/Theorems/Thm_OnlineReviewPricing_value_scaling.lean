-- Prove2me | Theorems.Thm_OnlineReviewPricing_value_scaling
-- name    : OnlineReviewPricing.value_scaling
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:29:49.676829+00:00
-- url     : https://prove2.me/theorems/a932d334-68ad-4610-95ed-8d88590c0c3f
-- title:
--   (EC.26), p.ec13 — $\bar J^*_T/T$ depends only on $\gamma T$, with its limit (corrected: a best root, not a unique one)
-- statement:
--   The ratio $\bar J^*_T/T$ depends on $(\gamma,T)$ only through the product $\gamma T$. Moreover, for every $\kappa>0$, the equation
--
--   $$
--   z+\exp(z)=\mu-1+\frac{\mu_0-\mu}{\kappa\ell(z)+1}
--   $$
--
--   has a root at which the expression below is largest among all roots, and at every such root $z_\kappa$,
--
--   $$
--   \frac{\bar J^*_T}{T}\to\exp(z_\kappa)+\frac{\mu_0-\mu}{\kappa}\left(\log\bigl(\kappa\ell(z_\kappa)+1\bigr)-\frac{\kappa\ell(z_\kappa)}{\kappa\ell(z_\kappa)+1}\right)\qquad\text{as }\gamma T\to\kappa,
--   $$
--
--   where the limit is taken over all pairs $\gamma,T>0$.
--
--   This is the reason the regimes of the paper are indexed by $\gamma T$.
--
--   Differences from the source:
--   - correction: z_κ 'is unique by Theorem 1' → z_κ is any root that is best among the roots; reason: the printed claim needs (15), and (15) is not an assumption here: µ = 29, µ₀ = −11, κ = 100 gives the three roots z ≈ −11.97, −6.42, 3.19
--   - generalization: the limit as γT → κ, with T fixed in the proof → exact dependence on γT alone, for all pairs, together with the limit; reason: the exact statement contains the page's limit and justifies its 'without loss of generality, we fix T'
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
--   - encoding: J̄*_T = max over Ψ → sSup of the set of admissible revenues; reason: the set is nonempty and bounded above and the supremum is attained (Theorem 1), so the value is the same
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.26), p.ec13 (PDF 50)

import Mathlib
import Definitions.Def_OnlineReviewPricing_fluidValue
import Definitions.Def_OnlineReviewPricing_IsCriticalRoot
import Definitions.Def_OnlineReviewPricing_criticalValue

open Filter Topology

namespace OnlineReviewPricing

/-- `J̄*_T / T` is a function of `γ T` alone. For `κ > 0`, the limit equation has a best root, and
at every best root `z`, `J̄*_T / T` tends to the right side of (EC.26) as `γ T → κ`, over all pairs
`γ, T > 0` (Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.26), p.ec13).

**Formalization Note.** The page says the root is "unique by Theorem 1", which needs (15). Without
(15) the limit equation can have several roots, and the limit is the value at a best root. -/
theorem value_scaling (μ μ₀ : ℝ) :
    (∀ γ T γ' T' : ℝ, 0 < γ → 0 < T → 0 < γ' → 0 < T' → γ * T = γ' * T' →
      fluidValue μ μ₀ γ T / T = fluidValue μ μ₀ γ' T' / T') ∧
    ∀ κ : ℝ, 0 < κ →
      (∃ z, IsCriticalRoot μ μ₀ κ z ∧
        ∀ z', IsCriticalRoot μ μ₀ κ z' → criticalValue μ μ₀ κ z' ≤ criticalValue μ μ₀ κ z) ∧
      ∀ z, IsCriticalRoot μ μ₀ κ z →
        (∀ z', IsCriticalRoot μ μ₀ κ z' → criticalValue μ μ₀ κ z' ≤ criticalValue μ μ₀ κ z) →
        Tendsto (fun x : ℝ × ℝ => fluidValue μ μ₀ x.1 x.2 / x.2)
          (comap (fun x : ℝ × ℝ => x.1 * x.2) (𝓝 κ) ⊓ 𝓟 {x | 0 < x.1 ∧ 0 < x.2})
          (𝓝 (criticalValue μ μ₀ κ z)) := by sorry

end OnlineReviewPricing
