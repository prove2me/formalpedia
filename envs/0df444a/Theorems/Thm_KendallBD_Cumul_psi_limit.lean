-- Prove2me | Theorems.Thm_KendallBD_Cumul_psi_limit
-- name    : KendallBD.Cumul.psi_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:27:43.72299+00:00
-- url     : https://prove2.me/theorems/0421fc00-8d2c-4feb-9fc7-d70edc8f3e6c
-- title:
--   §5, (51), p. 11 — ψ(1, w, ∞) = wα = [λ₀ + μ₀ − √{(λ₀+μ₀)² − 4λ₀μ₀w}]/(2λ₀)
-- statement:
--   Let $0 < \lambda_0 \le \mu_0$ (a transient process), let $0 < w < 1$, and let $\psi$ be the generating function (50), with $\alpha$ the smaller root of $\lambda_0 w z^2 - (\lambda_0 + \mu_0) z + \mu_0 = 0$. Then as $t \to \infty$
--   $$\psi(1, w, t) \longrightarrow w\alpha, \qquad\text{and}\qquad w\alpha = \frac{\lambda_0 + \mu_0 - \sqrt{(\lambda_0 + \mu_0)^2 - 4\lambda_0\mu_0 w}}{2\lambda_0}, \tag{51}$$
--   with the positive square root.
--
--   The function $\psi(1, w, t)$ is the generating function of the cumulative population $M_t$ alone, so its limit determines the asymptotic distribution of $M_\infty$.
--
--   **Formalization Note.** "$\psi(1, w, \infty)$" is read as the limit of $\psi(1, w, t)$ as $t \to \infty$, for each fixed $w \in (0, 1)$; `Real.sqrt` is the nonnegative square root.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §5, (51), p. 11

import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting
open Filter Topology

namespace KendallBD.Cumul

theorem psi_limit (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    ∀ w ∈ Set.Ioo (0:ℝ) 1,
      Tendsto (fun t => psi lam0 mu0 1 w t) atTop (𝓝 (w * alpha lam0 mu0 w)) ∧
      w * alpha lam0 mu0 w
        = (lam0 + mu0 - Real.sqrt ((lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w)) / (2 * lam0) := by sorry

end KendallBD.Cumul
