-- Prove2me | Theorems.Thm_HessianDamping_DINSC_lyap_deriv_ineq
-- name    : HessianDamping.DINSC.lyap_deriv_ineq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:01.781185+00:00
-- url     : https://prove2.me/theorems/1adc96ab-c7ae-4d2b-8e90-3ab32e95179b
-- title:
--   Proof of Theorem 7, p. 20 — d/dt E + √μ(E + ½‖ẋ‖² + (β/√μ − β²/2)‖∇f(x)‖² − β√μ⟨x − x⋆, ∇f(x)⟩) ≤ 0
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $f:\mathcal H\to\mathbb R$ convex of class $\mathcal C^2$ and $\mu$-strongly convex for some $\mu>0$, with minimizer $x^\star$. Let $t_0>0$, $\beta\in\mathbb R$, and let $x:[t_0,+\infty[\to\mathcal H$ be a solution of
--   $$\ddot x(t)+2\sqrt{\mu}\,\dot x(t)+\beta\nabla^2 f(x(t))\dot x(t)+\nabla f(x(t))=0 .$$
--   Let $\mathcal E(t)=f(x(t))-f(x^\star)+\frac12\|\sqrt{\mu}(x(t)-x^\star)+\dot x(t)+\beta\nabla f(x(t))\|^2$. Then for every $t\ge t_0$, $\mathcal E$ is differentiable at $t$ (from the right at $t_0$), and, writing $x=x(t)$, $\dot x=\dot x(t)$,
--   $$\frac{d}{dt}\mathcal E(t)+\sqrt{\mu}\Big(\mathcal E(t)+\tfrac12\|\dot x\|^2+\Big(\frac{\beta}{\sqrt\mu}-\frac{\beta^2}{2}\Big)\|\nabla f(x)\|^2-\beta\sqrt{\mu}\,\langle x-x^\star,\nabla f(x)\rangle\Big)\le 0 .$$
--
--   This is the first form of the differential inequality for the Lyapunov function in the proof of Theorem 7; the bound on $\beta$ is used only afterwards.
--
--   **Formalization Note.** The derivative is a one-sided derivative within $[t_0,+\infty[$, stated as the existence of a number $\mathcal E'$ which is that derivative and satisfies the inequality; such a derivative is unique. The page proves this step under the hypothesis $0\le\beta\le 1/(2\sqrt\mu)$ of Theorem 7, but the computation uses only (19) and strong convexity, so no bound on $\beta$ is assumed here.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 20, §4.1, proof of Theorem 7 (i), display after 'After developing and simplifying, we obtain'

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.DINSC

open Set

/-- Proof of Theorem 7, p. 20: the derivative `E'` of the Lyapunov function satisfies
`E' + √μ (E + ½‖ẋ‖² + (β/√μ − β²/2)‖∇f(x)‖² − β√μ ⟨x − x⋆, ∇f(x)⟩) ≤ 0`.
No bound on `β` is assumed: this step uses only (19) and strong convexity. -/
theorem lyap_deriv_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC2 : ContDiff ℝ 2 f)
    (μ : ℝ) (hμ : 0 < μ) (hsc : IsStronglyConvex f μ)
    (xstar : H) (hxstar : ∀ y, f xstar ≤ f y)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (β : ℝ)
    (x xd xdd : ℝ → H) (hx : IsSolution19 f μ β t₀ x xd xdd) :
    ∀ t ∈ Ici t₀, ∃ E' : ℝ, HasDerivWithinAt (lyap f μ β xstar x xd) E' (Ici t₀) t ∧
      E' + Real.sqrt μ * (lyap f μ β xstar x xd t + 1 / 2 * ‖xd t‖ ^ 2
        + (β / Real.sqrt μ - β ^ 2 / 2) * ‖gradient f (x t)‖ ^ 2
        - β * Real.sqrt μ * inner ℝ (x t - xstar) (gradient f (x t))) ≤ 0 := by sorry

end HessianDamping.DINSC
