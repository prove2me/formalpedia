-- Prove2me | Theorems.Thm_OnlineReviewPricing_closed_form_value
-- name    : OnlineReviewPricing.closed_form_value
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:29:46.687554+00:00
-- url     : https://prove2.me/theorems/3a728f7f-b5a6-48c1-b827-6379b99b2c41
-- title:
--   (16), Remark 2, p.14 — the closed-form value at a best root of (14)
-- statement:
--   Let $\gamma,T>0$. For every root $z$ of (14), the revenue of the path (13) at $z$ is
--
--   $$
--   \exp(z)T+\frac{\mu_0-\mu}{\gamma}\left(\log\bigl(\gamma\ell(z)T+1\bigr)-\frac{\gamma\ell(z)T}{\gamma\ell(z)T+1}\right). \tag{16}
--   $$
--
--   Moreover (14) has a root $z^*$ at which this expression is largest among all roots, the path (13) at $z^*$ is optimal, and $\bar J^*_T$ equals (16) at $z^*$.
--
--   So the closed form holds with no restriction on the parameters, in particular without condition (15).
--
--   Differences from the source:
--   - reading: 'one may choose the value of z* that corresponds to a greater value of the objective function' → a root maximizing (16) among all roots exists, and its path (13) is optimal; reason: the remark does not say that the chosen root solves (10); the stated reading is the one the proof of Theorem 3 needs, and it is true without (15)
--   - reading: 'piecewise continuous paths', with no further detail → continuous off a finite subset of [0, T], with finite one-sided limits at every point; reason: this is the standard meaning, it makes prices bounded, and without it the revenue integral need not exist
--   - encoding: the differential equation ṅ = λ(p, n) → its integral form on [0, T]; reason: the integrand is bounded and measurable, and this is the equation's meaning at the discontinuities of a piecewise continuous p
--   - encoding: J̄*_T = max over Ψ → sSup of the set of admissible revenues; reason: the set is nonempty and bounded above and the supremum is attained (Theorem 1), so the value is the same
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (16), Remark 2, p.14

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsOptimalPath
import Definitions.Def_OnlineReviewPricing_IsRootOf14
import Definitions.Def_OnlineReviewPricing_candidatePrice
import Definitions.Def_OnlineReviewPricing_candidatePath
import Definitions.Def_OnlineReviewPricing_fluidRevenue
import Definitions.Def_OnlineReviewPricing_fluidValue
import Definitions.Def_OnlineReviewPricing_closedFormValue

namespace OnlineReviewPricing

/-- Each root of (14) has revenue given by the right side of (16) along its path (13). A best root
exists, its path is optimal, and the value of (10) is (16) at that root, with no assumption (15)
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), Remark 2, (16), p.14). -/
theorem closed_form_value (μ μ₀ γ T : ℝ) (hγ : 0 < γ) (hT : 0 < T) :
    (∀ z, IsRootOf14 μ μ₀ γ T z →
      fluidRevenue μ μ₀ γ T (candidatePrice μ μ₀ γ T z) (candidatePath z) =
        closedFormValue μ μ₀ γ T z) ∧
    ∃ z, IsRootOf14 μ μ₀ γ T z ∧
      (∀ z', IsRootOf14 μ μ₀ γ T z' → closedFormValue μ μ₀ γ T z' ≤ closedFormValue μ μ₀ γ T z) ∧
      IsOptimalPath μ μ₀ γ T (candidatePrice μ μ₀ γ T z) (candidatePath z) ∧
      fluidValue μ μ₀ γ T = closedFormValue μ μ₀ γ T z := by sorry

end OnlineReviewPricing
