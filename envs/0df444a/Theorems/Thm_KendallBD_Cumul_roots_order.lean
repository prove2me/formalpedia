-- Prove2me | Theorems.Thm_KendallBD_Cumul_roots_order
-- name    : KendallBD.Cumul.roots_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:26:52.318986+00:00
-- url     : https://prove2.me/theorems/ce6c88b7-0cdd-43de-bb11-ac8178169480
-- title:
--   §5, (49), pp. 10–11 — the roots of λ₀wz² − (λ₀+μ₀)z + μ₀ = 0 satisfy 0 < α < 1 < β for 0 < w < 1
-- statement:
--   Let $0 < \lambda_0 \le \mu_0$ be constant birth and death rates of a transient simple birth-and-death process, and let $0 < w < 1$. Then the quadratic (49)
--   $$\lambda_0 w z^2 - (\lambda_0 + \mu_0) z + \mu_0 = 0$$
--   has positive discriminant $(\lambda_0 + \mu_0)^2 - 4\lambda_0\mu_0 w > 0$; the numbers
--   $$\alpha = \frac{\lambda_0 + \mu_0 - \sqrt{(\lambda_0 + \mu_0)^2 - 4\lambda_0\mu_0 w}}{2\lambda_0 w}, \qquad \beta = \frac{\lambda_0 + \mu_0 + \sqrt{(\lambda_0 + \mu_0)^2 - 4\lambda_0\mu_0 w}}{2\lambda_0 w}$$
--   are both roots of it; and
--   $$0 < \alpha < 1 < \beta.$$
--
--   This is the choice of roots with which Kendall writes the general solution of the equation (31) for the joint generating function of the population size and the cumulative population.
--
--   **Formalization Note.** The page says "so chosen that $0 < \alpha < 1 < \beta$" under the standing assumption $\lambda_0 \le \mu_0$. At $w = 1$ with $\lambda_0 < \mu_0$ the roots are $1$ and $\mu_0/\lambda_0$, so the strict ordering holds only for $0 < w < 1$, which is the range stated here; this range determines all coefficients of a power series in $w$.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §5, (49) and the sentence following it, pp. 10–11

import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting
open Filter Topology

namespace KendallBD.Cumul

theorem roots_order (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    ∀ w ∈ Set.Ioo (0:ℝ) 1,
      0 < disc lam0 mu0 w ∧
      lam0 * w * alpha lam0 mu0 w ^ 2 - (lam0 + mu0) * alpha lam0 mu0 w + mu0 = 0 ∧
      lam0 * w * beta lam0 mu0 w ^ 2 - (lam0 + mu0) * beta lam0 mu0 w + mu0 = 0 ∧
      0 < alpha lam0 mu0 w ∧ alpha lam0 mu0 w < 1 ∧ 1 < beta lam0 mu0 w := by sorry

end KendallBD.Cumul
