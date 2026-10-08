-- Prove2me | Theorems.Thm_HessianDamping_DINSC_lyap_deriv_le
-- name    : HessianDamping.DINSC.lyap_deriv_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:00.73817+00:00
-- url     : https://prove2.me/theorems/47d1dbe6-b66b-4fcf-b495-f7af357ecf2e
-- title:
--   Proof of Theorem 7, p. 21 — for 0 ≤ β ≤ 1/(2√μ), d/dt E(t) + (√μ/2)E(t) + (√μ/2)‖ẋ(t)‖² ≤ 0
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ convex of class $\mathcal C^2$ and $\mu$-strongly convex for some $\mu>0$, with minimizer $x^\star$. Let $t_0>0$, $0\le\beta\le\frac1{2\sqrt\mu}$, and let $x:[t_0,+\infty[\to\mathcal H$ solve
--   $$\ddot x(t)+2\sqrt{\mu}\,\dot x(t)+\beta\nabla^2 f(x(t))\dot x(t)+\nabla f(x(t))=0 .$$
--   With $\mathcal E(t)=f(x(t))-f(x^\star)+\frac12\|\sqrt{\mu}(x(t)-x^\star)+\dot x(t)+\beta\nabla f(x(t))\|^2$, for every $t\ge t_0$ the function $\mathcal E$ is differentiable at $t$ (from the right at $t_0$) and
--   $$\frac{d}{dt}\mathcal E(t)+\frac{\sqrt\mu}{2}\mathcal E(t)+\frac{\sqrt\mu}{2}\|\dot x(t)\|^2\le 0 .$$
--
--   This is the clean differential inequality from which both the exponential decay of $\mathcal E$ and the weighted integrability of $\|\dot x\|^2$ in Theorem 7 follow.
--
--   **Formalization Note.** The derivative is a one-sided derivative within $[t_0,+\infty[$, stated as the existence of a number which is that derivative and satisfies the inequality.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 21, §4.1, proof of Theorem 7 (i), display after 'Hence for 0 ≤ β ≤ 1/(2√µ)'

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.DINSC

open Set

/-- Proof of Theorem 7, p. 21: for `0 ≤ β ≤ 1/(2√μ)`,
`E'(t) + (√μ/2) E(t) + (√μ/2)‖ẋ(t)‖² ≤ 0`. -/
theorem lyap_deriv_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ β t₀ x xd xdd) :
    ∀ t ∈ Ici t₀, ∃ E' : ℝ, HasDerivWithinAt (lyap f μ β xstar x xd) E' (Ici t₀) t ∧
      E' + Real.sqrt μ / 2 * lyap f μ β xstar x xd t + Real.sqrt μ / 2 * ‖xd t‖ ^ 2 ≤ 0 := by sorry

end HessianDamping.DINSC
