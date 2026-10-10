-- Prove2me | Theorems.Thm_HighResODE_NAGCODE_lyap_t0_bound
-- name    : HighResODE.NAGCODE.lyap_t0_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:50.931484+00:00
-- url     : https://prove2.me/theorems/805544ba-b5a4-42e2-8a94-18bb2b0e9768
-- title:
--   p. 22 — by the initial conditions of (1.12), E(t₀) ≤ 3s·(L/2)‖x₀ − x⋆‖² + 2‖x₀ − x⋆‖²
-- statement:
--   Let $f\in\mathcal F^2_L(\mathbb R^n)$, let $x^\star$ be a minimizer of $f$, let $s>0$ and $t_0=1.5\sqrt s$, and let $X$ solve the high-resolution ODE of NAG-C (1.12) from $x_0$, with Lyapunov function $\mathcal E$ of (4.1). Then
--   $$\mathcal E(t_0)=t_0\Big(t_0+\frac{\sqrt s}{2}\Big)\big(f(x_0)-f(x^\star)\big)+\frac12\big\|-t_0\sqrt s\,\nabla f(x_0)+2(x_0-x^\star)+t_0\sqrt s\,\nabla f(x_0)\big\|^2\le3s\cdot\frac L2\|x_0-x^\star\|^2+2\|x_0-x^\star\|^2 .$$
--
--   The equality evaluates (4.1) at the initial conditions $X(t_0)=x_0$, $\dot X(t_0)=-\sqrt s\nabla f(x_0)$; the bound gives the constant $2+1.5sL$ of (4.4).
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 22, display after (4.3)

import Mathlib
import Definitions.Def_HighResODE_NAGCODE_Setting

namespace HighResODE.NAGCODE

open scoped InnerProductSpace

/-- p. 22: by the initial conditions of (1.12),
`E(t₀) = t₀(t₀ + √s/2)(f(x₀) − f(x⋆)) + ½‖−t₀√s∇f(x₀) + 2(x₀ − x⋆) + t₀√s∇f(x₀)‖² ≤ 3s·(L/2)‖x₀ − x⋆‖² + 2‖x₀ − x⋆‖²`. -/
theorem lyap_t0_bound {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : IsF2 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsNAGCODE f s x0 X V) :
    lyap f s xs X V (t0 s)
        = t0 s * (t0 s + Real.sqrt s / 2) * (f x0 - f xs)
          + 1 / 2 * ‖-(t0 s * Real.sqrt s) • gradient f x0 + (2 : ℝ) • (x0 - xs)
            + (t0 s * Real.sqrt s) • gradient f x0‖ ^ 2 ∧
      lyap f s xs X V (t0 s) ≤ 3 * s * (L / 2) * ‖x0 - xs‖ ^ 2 + 2 * ‖x0 - xs‖ ^ 2 := by sorry

end HighResODE.NAGCODE
