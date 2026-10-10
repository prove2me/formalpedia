-- Prove2me | Theorems.Thm_HighResODE_HeavyBallODE_theorem_2
-- name    : HighResODE.HeavyBallODE.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:16.491955+00:00
-- url     : https://prove2.me/theorems/ab58c4d1-8711-4bbe-b862-9d03cda45955
-- title:
--   Theorem 2, p. 14 — for f ∈ S²_{μ,L} and 0 < s ≤ 1/L, the high-resolution heavy-ball ODE satisfies f(X(t)) − f(x⋆) ≤ 7‖x₀ − x⋆‖² e^{−√μ t/4}/(2s)
-- statement:
--   **Theorem 2 (Convergence of the heavy-ball ODE).** Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$, that is, $f$ is twice continuously differentiable with Lipschitz-continuous Hessian, $L$-smooth, and $\mu$-strongly convex with $0<\mu\le L$, and let $x^\star$ be its minimizer. Fix a step size $0<s\le 1/L$ and an initial point $x_0\in\mathbb R^n$, and let $X=X(t)$ be the solution of the high-resolution ODE of the heavy-ball method,
--   $$\ddot X(t)+2\sqrt\mu\,\dot X(t)+\bigl(1+\sqrt{\mu s}\bigr)\nabla f(X(t))=0,\qquad X(0)=x_0,\quad\dot X(0)=-\frac{2\sqrt s\,\nabla f(x_0)}{1+\sqrt{\mu s}} .$$
--   Then for every $t\ge0$,
--   $$f(X(t))-f(x^\star)\le\frac{7\,\|x_0-x^\star\|^2}{2s}\,e^{-\sqrt\mu\,t/4}.$$
--
--   The high-resolution ODE keeps the $O(\sqrt s)$ terms that the classical low-resolution limit discards. The theorem shows that this continuous-time model of Polyak's heavy-ball method converges linearly at the accelerated rate $e^{-\sqrt\mu t/4}$; in the paper it is contrasted with the high-resolution ODE of NAG-SC (Theorem 1), which carries an additional gradient-correction term.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The solution is any pair $(X,V)$ of curves with $V$ the derivative of $X$ and $-2\sqrt\mu V-(1+\sqrt{\mu s})\nabla f(X)$ the derivative of $V$ on $[0,\infty)$ (one-sided at $0$), satisfying the two initial conditions; since the solution is unique (Proposition 2.1 of the paper), quantifying over all solutions is the paper's statement. The minimizer is a point $x^\star$ with $f(x^\star)\le f(z)$ for all $z$, which exists for strongly convex $f$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 14, Theorem 2

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

namespace HighResODE.HeavyBallODE

theorem theorem_2 {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / L) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsHeavyBallODE f μ s x0 X V) :
    ∀ t : ℝ, 0 ≤ t →
      f (X t) - f xs ≤ 7 * ‖x0 - xs‖ ^ 2 / (2 * s) * Real.exp (-(Real.sqrt μ * t / 4)) := by sorry

end HighResODE.HeavyBallODE
