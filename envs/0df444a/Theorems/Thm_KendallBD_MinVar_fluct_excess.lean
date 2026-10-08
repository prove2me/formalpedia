-- Prove2me | Theorems.Thm_KendallBD_MinVar_fluct_excess
-- name    : KendallBD.MinVar.fluct_excess
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:48.508016+00:00
-- url     : https://prove2.me/theorems/f71f18b0-184b-43d6-855e-156bdc270068
-- title:
--   §6, p. 12 — variance exceeds the minimum by the common birth-and-death rate
-- statement:
--   Let $\bar n$ be a positive $C^1$ mean curve with $\bar n_0=1$. Let continuous nonnegative rates $\lambda,\mu$ produce this mean, and let $\lambda_*,\mu_*$ be Kendall's rate pair from the positive and negative parts of $\bar n'/\bar n$. Then for every $t\ge0$,
--
--   $$
--   V_{\lambda,\mu}(t)=V_{\lambda_*,\mu_*}(t)
--     +2e^{-2\rho(t)}\int_0^t e^{\rho(\tau)}\min\{\lambda(\tau),\mu(\tau)\}\,d\tau.
--   $$
--
--   The last term makes explicit Kendall's statement that the rate-dependent excess is nonnegative and vanishes for his chosen rates.
--
--   **Formalization Note** This is a pointwise positive-and-negative-part restatement of the displayed three-region decomposition on p. 12. It does not require a partition into intervals of monotonicity.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §6, unnumbered variance decomposition and the paragraph before (56), p. 12

import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting

namespace KendallBD.MinVar

/-- The nonnegative excess term in Kendall's minimum-fluctuation argument,
§6, p. 12, following the variance decomposition. -/
theorem fluct_excess (nbar lam mu : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1)
    (hadm : Admissible lam mu) (hmean : HasMean lam mu nbar) :
    ∀ t : ℝ, 0 ≤ t →
      fluct lam mu t = fluct (lamStar nbar) (muStar nbar) t +
        2 * Real.exp (-2 * KendallBD.Sol.rho lam mu t) *
          ∫ τ in (0 : ℝ)..t,
            Real.exp (KendallBD.Sol.rho lam mu τ) * min (lam τ) (mu τ) := by sorry

end KendallBD.MinVar
