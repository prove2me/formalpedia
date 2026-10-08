-- Prove2me | Theorems.Thm_KendallBD_Cumul_psi_solves
-- name    : KendallBD.Cumul.psi_solves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:26:39.069994+00:00
-- url     : https://prove2.me/theorems/7bef10ed-5b56-40c9-a550-daea6f30472a
-- title:
--   §5, (50), p. 11 — ψ of (50) solves ∂ψ/∂t = {λ₀wz² − (λ₀+μ₀)z + μ₀}∂ψ/∂z with ψ(z, w, 0) = zw
-- statement:
--   Let $0 < \lambda_0 \le \mu_0$ be constant birth and death rates, let $0 < w < 1$, and let $\alpha, \beta$ be the roots of (49), $\lambda_0 w z^2 - (\lambda_0 + \mu_0) z + \mu_0 = 0$, with $\alpha$ the smaller one. Define
--   $$\psi(z, w, t) = w\,\frac{\alpha(\beta - z) + \beta(z - \alpha)e^{-\lambda_0 w(\beta - \alpha)t}}{(\beta - z) + (z - \alpha)e^{-\lambda_0 w(\beta - \alpha)t}}. \tag{50}$$
--   Then:
--
--   1. for every $z \in [0, 1]$ and every $t \ge 0$, both partial derivatives of $\psi$ exist at $(z, w, t)$ and
--   $$\frac{\partial \psi}{\partial t} = \{\lambda_0 w z^2 - (\lambda_0 + \mu_0) z + \mu_0\}\frac{\partial \psi}{\partial z}; \tag{31}$$
--   2. for every real $z$, $\psi(z, w, 0) = zw$ (the boundary condition (32), for an initial population $n_0 = M_0 = 1$).
--
--   So (50) is the solution of the equation for the joint generating function of the population size $n_t$ and the cumulative population $M_t$ when the rates are constant.
--
--   **Formalization Note.** The equation is stated pointwise with explicit derivatives (`HasDerivAt` in $t$ and in $z$), on $z \in [0, 1]$, $t \ge 0$, the range of a probability generating function, where the denominator of (50) is positive.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §5, (50), p. 11, with §4, (31)–(32), p. 8

import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting
open Filter Topology

namespace KendallBD.Cumul

theorem psi_solves (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    ∀ w ∈ Set.Ioo (0:ℝ) 1,
      (∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t → SolvesPDE lam0 mu0 (psi lam0 mu0) z w t) ∧
      ∀ z : ℝ, psi lam0 mu0 z w 0 = z * w := by sorry

end KendallBD.Cumul
