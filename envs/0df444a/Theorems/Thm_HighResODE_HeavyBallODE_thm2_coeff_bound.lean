-- Prove2me | Theorems.Thm_HighResODE_HeavyBallODE_thm2_coeff_bound
-- name    : HighResODE.HeavyBallODE.thm2_coeff_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:55.110265+00:00
-- url     : https://prove2.me/theorems/6477c482-d9a5-4f08-85d0-7d7b9d0845e9
-- title:
--   Proof of Theorem 2, p. 14 — f(X) − f(x⋆) ≤ [1/2 + 3/(1 + √(μs))³ + 2(μs)/(1 + √(μs))]‖x₀ − x⋆‖² e^{−√μ t/4}/s
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$ with minimizer $x^\star$, let the step size satisfy $0<s\le1/L$, and let $X=X(t)$ be the solution of the high-resolution heavy-ball ODE (1.10) with $X(0)=x_0$ and $\dot X(0)=-2\sqrt s\,\nabla f(x_0)/(1+\sqrt{\mu s})$. Then for every $t\ge0$,
--   $$f(X(t))-f(x^\star)\le\left[\frac12+\frac{3}{(1+\sqrt{\mu s})^3}+\frac{2(\mu s)}{1+\sqrt{\mu s}}\right]\frac{\|x_0-x^\star\|^2\,e^{-\sqrt\mu\,t/4}}{s}.$$
--
--   This is the bound with an explicit, step-size-dependent coefficient from which Theorem 2 follows once the coefficient is shown to be below $7/2$.
--
--   **Formalization Note.** Hypotheses as in Theorem 2: $0<s\le1/L$, $x^\star$ a point with $f(x^\star)\le f(z)$ for all $z$, and $(X,V)$ any solution of (1.10) on $[0,\infty)$ with its initial conditions.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 14, proof sketch of Theorem 2, coefficient display

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

namespace HighResODE.HeavyBallODE

theorem thm2_coeff_bound {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / L) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsHeavyBallODE f μ s x0 X V) :
    ∀ t : ℝ, 0 ≤ t →
      f (X t) - f xs ≤
        (1 / 2 + 3 / (1 + Real.sqrt (μ * s)) ^ 3 + 2 * (μ * s) / (1 + Real.sqrt (μ * s)))
          * ‖x0 - xs‖ ^ 2 * Real.exp (-(Real.sqrt μ * t / 4)) / s := by sorry

end HighResODE.HeavyBallODE
