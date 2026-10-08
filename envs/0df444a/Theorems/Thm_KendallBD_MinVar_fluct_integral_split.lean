-- Prove2me | Theorems.Thm_KendallBD_MinVar_fluct_integral_split
-- name    : KendallBD.MinVar.fluct_integral_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:56.986993+00:00
-- url     : https://prove2.me/theorems/99375a24-9c5c-4c46-8ab1-50ad8a0236c9
-- title:
--   §6, variance decomposition, p. 12 — interval identities behind the three-region split
-- statement:
--   Let $\lambda,\mu$ be continuous nonnegative rates, and let $0\le a\le b$. With $\rho(t)=\int_0^t(\mu-\lambda)$, the variance integrand has two equivalent interval decompositions:
--
--   $$
--   \begin{aligned}
--   \int_a^b e^{\rho}(\lambda+\mu)
--     &=e^{\rho(b)}-e^{\rho(a)}+2\int_a^b e^{\rho}\lambda,\\
--     &=-\bigl(e^{\rho(b)}-e^{\rho(a)}\bigr)+2\int_a^b e^{\rho}\mu.
--   \end{aligned}
--   $$
--
--   Applied across the decreasing, increasing and constant intervals of a prescribed mean curve, these identities give the two endpoint-sum terms and the explicit nonnegative-rate terms in Kendall's displayed variance decomposition.
--
--   **Formalization Note** Each identity holds on any nonnegative-time interval. Kendall selects one or the other according to the monotonicity region of the mean.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §6, unnumbered display after "Then one can write", p. 12

import Mathlib
import Definitions.Def_KendallBD_MinVar_Setting

namespace KendallBD.MinVar

/-- The two interval identities behind Kendall's variance decomposition,
§6, display after "Then one can write", p. 12. -/
theorem fluct_integral_split (lam mu : ℝ → ℝ)
    (hadm : Admissible lam mu) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)) =
        (Real.exp (KendallBD.Sol.rho lam mu b) - Real.exp (KendallBD.Sol.rho lam mu a)) +
          2 * ∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * lam τ ∧
    (∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * (lam τ + mu τ)) =
        -(Real.exp (KendallBD.Sol.rho lam mu b) - Real.exp (KendallBD.Sol.rho lam mu a)) +
          2 * ∫ τ in a..b, Real.exp (KendallBD.Sol.rho lam mu τ) * mu τ := by sorry

end KendallBD.MinVar
