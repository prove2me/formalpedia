-- Prove2me | Theorems.Thm_HessianDamping_DINSC_Z_deriv_le
-- name    : HessianDamping.DINSC.Z_deriv_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:50.70058+00:00
-- url     : https://prove2.me/theorems/aa06fd33-ef17-48a5-9c58-5fd9f3257ce9
-- title:
--   Proof of Theorem 7 (ii), p. 21 — d/dt Z(t) + √μ Z(t) + β²‖∇f(x(t))‖² ≤ Ce^{−(√μ/2)t}, C = 2E(t₀)e^{(√μ/2)t₀}
-- statement:
--   Under the hypotheses of Theorem 7 — $\mathcal H$ a real Hilbert space, $f$ convex of class $\mathcal C^2$ and $\mu$-strongly convex ($\mu>0$) with minimizer $x^\star$, $t_0>0$, $0\le\beta\le\frac1{2\sqrt\mu}$, and $x$ a solution of
--   $$\ddot x(t)+2\sqrt{\mu}\,\dot x(t)+\beta\nabla^2 f(x(t))\dot x(t)+\nabla f(x(t))=0$$
--   on $[t_0,+\infty[$ — let
--   $$Z(t):=2\beta\big(f(x(t))-f(x^\star)\big)+\sqrt\mu\,\|x(t)-x^\star\|^2,\qquad C:=2\,\mathcal E(t_0)\,e^{\frac{\sqrt\mu}{2}t_0},$$
--   where $\mathcal E(t_0)=f(x(t_0))-f(x^\star)+\frac12\|\sqrt\mu(x(t_0)-x^\star)+\dot x(t_0)+\beta\nabla f(x(t_0))\|^2$. Then for every $t\ge t_0$, $Z$ is differentiable at $t$ (from the right at $t_0$) and
--   $$\frac{d}{dt}Z(t)+\sqrt\mu\,Z(t)+\beta^2\|\nabla f(x(t))\|^2\le C\,e^{-\frac{\sqrt\mu}{2}t}.$$
--
--   Integrating this inequality against $e^{\sqrt\mu t}$ yields the averaged exponential decay of the gradients in Theorem 7 (ii).
--
--   **Formalization Note.** The derivative is a one-sided derivative within $[t_0,+\infty[$, stated as the existence of a number which is that derivative and satisfies the inequality.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 21, §4.1, proof of Theorem 7 (ii), display after 'Set Z(t) := 2β(f(x(t)) − f(x⋆)) + √µ‖x(t) − x⋆‖². We have'

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.DINSC

open Set

/-- Proof of Theorem 7 (ii), p. 21: with `C = 2E(t₀)e^{(√μ/2)t₀}`, the derivative `Z'` of
`Z(t) = 2β(f(x(t)) − f(x⋆)) + √μ‖x(t) − x⋆‖²` satisfies
`Z'(t) + √μ Z(t) + β²‖∇f(x(t))‖² ≤ C e^{−(√μ/2)t}`. -/
theorem Z_deriv_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ β t₀ x xd xdd) :
    ∀ t ∈ Ici t₀, ∃ Z' : ℝ, HasDerivWithinAt (Zfun f μ β xstar x) Z' (Ici t₀) t ∧
      Z' + Real.sqrt μ * Zfun f μ β xstar x t + β ^ 2 * ‖gradient f (x t)‖ ^ 2 ≤
        2 * lyap f μ β xstar x xd t₀ * Real.exp (Real.sqrt μ / 2 * t₀)
          * Real.exp (-(Real.sqrt μ / 2) * t) := by sorry

end HessianDamping.DINSC
