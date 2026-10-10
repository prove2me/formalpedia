-- Prove2me | Theorems.Thm_HighResODE_NAGSCODE_theorem_1
-- name    : HighResODE.NAGSCODE.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:32.257273+00:00
-- url     : https://prove2.me/theorems/214614be-3797-48cd-b05f-196a904a2825
-- title:
--   Theorem 1, p. 13 — for f ∈ S²_{μ,L} and 0 < s ≤ 1/L, the NAG-SC high-resolution ODE satisfies f(X(t)) − f(x⋆) ≤ (2‖x₀ − x⋆‖²/s) e^{−√μ t/4}
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$, that is, $f$ is $L$-smooth, $\mu$-strongly convex with $0<\mu\le L$, of class $C^2$ with a Lipschitz-continuous Hessian, and let $x^\star$ be its minimizer. Let $0<s\le1/L$ be a step size and $x_0\in\mathbb R^n$. Let $X=X(t)$ be the solution of the high-resolution ODE of NAG-SC,
--   $$\ddot X(t)+2\sqrt\mu\,\dot X(t)+\sqrt s\,\nabla^2 f(X(t))\dot X(t)+\big(1+\sqrt{\mu s}\big)\nabla f(X(t))=0,\qquad X(0)=x_0,\ \dot X(0)=-\frac{2\sqrt s\,\nabla f(x_0)}{1+\sqrt{\mu s}}.$$
--   Then for every $t\ge0$,
--   $$f(X(t))-f(x^\star)\le\frac{2\|x_0-x^\star\|^2}{s}\,e^{-\frac{\sqrt\mu t}{4}}.$$
--
--   The function value along the high-resolution ODE of Nesterov's accelerated gradient method for strongly convex functions converges linearly, at the accelerated rate $\sqrt\mu$ rather than $\mu$; with $s=1/L$ the bound reads $f(X)-f(x^\star)\le2L\|x_0-x^\star\|^2e^{-\sqrt\mu t/4}$. It is the continuous-time counterpart of the discrete rate for NAG-SC in Theorem 3 of the same paper.
--
--   **Formalization Note.** A solution is any pair of curves $(X,V)$ with $V$ the one-sided derivative of $X$ on $[0,\infty)$, $V$ having the derivative the ODE prescribes, and the initial conditions above; existence and uniqueness (Proposition 2.1) are not assumed, so "the solution" is read as "every solution". The minimizer $x^\star$ is a point with $f(x^\star)\le f(z)$ for all $z$. $\nabla^2 f(X)\dot X$ is the Fréchet derivative of $\nabla f$ at $X$ applied to $\dot X$. The Hessian's Lipschitz constant is not fixed.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 13, Theorem 1

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

open scoped InnerProductSpace

namespace HighResODE.NAGSCODE

theorem theorem_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (x0 : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n))
    (hsol : IsNAGSCODE f μ s x0 X V) :
    ∀ t, 0 ≤ t →
      f (X t) - f xs ≤ 2 * ‖x0 - xs‖ ^ 2 / s * Real.exp (-(Real.sqrt μ * t / 4)) := by sorry

end HighResODE.NAGSCODE
