-- Prove2me | Theorems.Thm_KendallBD_MinVar_rate_difference
-- name    : KendallBD.MinVar.rate_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:26.885771+00:00
-- url     : https://prove2.me/theorems/d2e916d8-4d8f-43ab-a32c-cae09838a84c
-- title:
--   §6, (55), p. 11 — the rate difference is the logarithmic derivative of the mean
-- statement:
--   Let $\bar n$ be a positive $C^1$ mean curve with $\bar n_0=1$. Suppose continuous nonnegative rates $\lambda,\mu$ give this mean through $\bar n_t=e^{-\rho(t)}$, where $\rho(t)=\int_0^t(\mu-\lambda)$. Then, at every $t\ge0$,
--
--   $$
--   \lambda(t)-\mu(t)=\frac{\bar n_t'}{\bar n_t}=\frac{d}{dt}\log\bar n_t.
--   $$
--
--   This identity is the constraint that every rate pair with the prescribed mean must satisfy.
--
--   **Formalization Note** Continuity of the rates and $C^1$ regularity of the mean make the equality meaningful also at $t=0$ by continuity from the right.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §6, (55), p. 11

import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting

namespace KendallBD.MinVar

/-- Kendall (1948), (55), p. 11. -/
theorem rate_difference (nbar lam mu : ℝ → ℝ)
    (hn : ContDiff ℝ 1 nbar) (hpos : ∀ t, 0 < nbar t) (h0 : nbar 0 = 1)
    (hadm : Admissible lam mu) (hmean : HasMean lam mu nbar) :
    ∀ t : ℝ, 0 ≤ t → lam t - mu t = growth nbar t := by sorry

end KendallBD.MinVar
