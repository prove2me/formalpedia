-- Prove2me | Theorems.Thm_HighResODE_NAGSCODE_eq_3_5
-- name    : HighResODE.NAGSCODE.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:16.264778+00:00
-- url     : https://prove2.me/theorems/3433fee7-d385-41d7-ac5e-b55802f300d7
-- title:
--   (3.5), p. 15 — dE/dt ≤ −√μ(((1+√(μs))/2)(f(X)−f(x⋆)) + ‖Ẋ‖² + (3μ/4)‖X−x⋆‖² + (s/2)‖∇f(X)‖²)
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$ with minimizer $x^\star$, let $s>0$, let $X$ solve the high-resolution ODE (1.11) of NAG-SC with $X(0)=x_0$ and $\dot X(0)=-2\sqrt s\,\nabla f(x_0)/(1+\sqrt{\mu s})$, and let $\mathcal E$ be the Lyapunov function (2.4). Then for every $t\ge0$ the derivative of $\mathcal E$ at $t$ (from the right at $t=0$) exists and, with $X=X(t)$, $\dot X=\dot X(t)$,
--   $$\frac{d\mathcal E}{dt}\le-\sqrt\mu\left(\frac{1+\sqrt{\mu s}}{2}\big(f(X)-f(x^\star)\big)+\|\dot X\|^2+\frac{3\mu}{4}\|X-x^\star\|^2+\frac s2\|\nabla f(X)\|^2\right).$$
--
--   The bound follows from (3.4) once $\langle\nabla f(X),X-x^\star\rangle$ is bounded below by strong convexity; together with (3.6) it gives the decay rate $\sqrt\mu/4$ of Lemma 3.1.
--
--   **Formalization Note.** The derivative is one-sided within $[0,\infty)$ and is stated as the existence of a number that is the derivative and satisfies the bound. Every step size $s>0$ is allowed.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 15, proof of Lemma 3.1, (3.5)

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

open scoped InnerProductSpace

namespace HighResODE.NAGSCODE

theorem eq_3_5 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xs ≤ f z) (hs : 0 < s)
    (x0 : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n))
    (hsol : IsNAGSCODE f μ s x0 X V) :
    ∀ t, 0 ≤ t → ∃ e' : ℝ, HasDerivWithinAt (lyap f μ s xs X V) e' (Set.Ici 0) t ∧
      e' ≤ -Real.sqrt μ * ((1 + Real.sqrt (μ * s)) / 2 * (f (X t) - f xs) + ‖V t‖ ^ 2
        + 3 * μ / 4 * ‖X t - xs‖ ^ 2 + s / 2 * ‖gradient f (X t)‖ ^ 2) := by sorry

end HighResODE.NAGSCODE
