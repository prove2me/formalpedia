-- Prove2me | Theorems.Thm_HighResODE_NAGSCODE_eq_3_4
-- name    : HighResODE.NAGSCODE.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:45.658987+00:00
-- url     : https://prove2.me/theorems/086df545-1e9a-4557-9743-c9ba43f26feb
-- title:
--   (3.4), proof of Lemma 3.1, p. 15 — dE/dt along the NAG-SC high-resolution ODE, its closed form and the bound −√μ(‖Ẋ‖² + (1+√(μs))⟨∇f(X), X−x⋆⟩ + (s/2)‖∇f(X)‖²)
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$ with minimizer $x^\star$, let $s>0$, and let $X$ solve the high-resolution ODE of NAG-SC
--   $$\ddot X+2\sqrt\mu\,\dot X+\sqrt s\,\nabla^2 f(X)\dot X+\big(1+\sqrt{\mu s}\big)\nabla f(X)=0,\qquad X(0)=x_0,\ \dot X(0)=-\frac{2\sqrt s\,\nabla f(x_0)}{1+\sqrt{\mu s}}.$$
--   Let $\mathcal E$ be the Lyapunov function (2.4). Then at every $t\ge0$ (from the right at $t=0$), $\mathcal E$ is differentiable, and with $X=X(t)$, $\dot X=\dot X(t)$,
--   $$\begin{aligned}\frac{d\mathcal E}{dt}&=\big(1+\sqrt{\mu s}\big)\langle\nabla f(X),\dot X\rangle+\frac12\Big\langle\dot X,-2\sqrt\mu\dot X-\sqrt s\nabla^2 f(X)\dot X-\big(1+\sqrt{\mu s}\big)\nabla f(X)\Big\rangle\\&\qquad+\frac12\Big\langle\dot X+2\sqrt\mu(X-x^\star)+\sqrt s\nabla f(X),-\big(1+\sqrt{\mu s}\big)\nabla f(X)\Big\rangle\\&=-\sqrt\mu\Big(\|\dot X\|^2+\big(1+\sqrt{\mu s}\big)\langle\nabla f(X),X-x^\star\rangle+\frac s2\|\nabla f(X)\|^2\Big)-\frac{\sqrt s}{2}\Big[\|\nabla f(X)\|^2+\dot X^\top\nabla^2 f(X)\dot X\Big]\\&\le-\sqrt\mu\Big(\|\dot X\|^2+\big(1+\sqrt{\mu s}\big)\langle\nabla f(X),X-x^\star\rangle+\frac s2\|\nabla f(X)\|^2\Big).\end{aligned}$$
--
--   This is the computation at the heart of Lemma 3.1: the first line differentiates (2.4) along the ODE, the second simplifies it, and the third drops the gradient-correction term, which is nonnegative because $f$ is convex.
--
--   **Formalization Note.** The derivative is one-sided within $[0,\infty)$; the statement asserts that the first expression is that derivative, that it equals the second, and that the second is at most the third. $\dot X$ is the velocity $V$ of the solution pair, and $\nabla^2 f(X)\dot X$ is the Fréchet derivative of $\nabla f$ at $X$ applied to $\dot X$. As in Lemma 3.1, every step size $s>0$ is allowed.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 15, proof of Lemma 3.1, (3.4)

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

open scoped InnerProductSpace

namespace HighResODE.NAGSCODE

theorem eq_3_4 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xs ≤ f z) (hs : 0 < s)
    (x0 : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n))
    (hsol : IsNAGSCODE f μ s x0 X V) :
    ∀ t, 0 ≤ t →
      HasDerivWithinAt (lyap f μ s xs X V)
        ((1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), V t⟫_ℝ
          + 1 / 2 * ⟪V t, -(2 * Real.sqrt μ) • V t
              - Real.sqrt s • fderiv ℝ (gradient f) (X t) (V t)
              - (1 + Real.sqrt (μ * s)) • gradient f (X t)⟫_ℝ
          + 1 / 2 * ⟪V t + (2 * Real.sqrt μ) • (X t - xs) + Real.sqrt s • gradient f (X t),
              -(1 + Real.sqrt (μ * s)) • gradient f (X t)⟫_ℝ)
        (Set.Ici 0) t ∧
      (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), V t⟫_ℝ
          + 1 / 2 * ⟪V t, -(2 * Real.sqrt μ) • V t
              - Real.sqrt s • fderiv ℝ (gradient f) (X t) (V t)
              - (1 + Real.sqrt (μ * s)) • gradient f (X t)⟫_ℝ
          + 1 / 2 * ⟪V t + (2 * Real.sqrt μ) • (X t - xs) + Real.sqrt s • gradient f (X t),
              -(1 + Real.sqrt (μ * s)) • gradient f (X t)⟫_ℝ
        = -Real.sqrt μ * (‖V t‖ ^ 2 + (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), X t - xs⟫_ℝ
              + s / 2 * ‖gradient f (X t)‖ ^ 2)
          - Real.sqrt s / 2 * (‖gradient f (X t)‖ ^ 2
              + ⟪V t, fderiv ℝ (gradient f) (X t) (V t)⟫_ℝ) ∧
      -Real.sqrt μ * (‖V t‖ ^ 2 + (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), X t - xs⟫_ℝ
              + s / 2 * ‖gradient f (X t)‖ ^ 2)
          - Real.sqrt s / 2 * (‖gradient f (X t)‖ ^ 2
              + ⟪V t, fderiv ℝ (gradient f) (X t) (V t)⟫_ℝ)
        ≤ -Real.sqrt μ * (‖V t‖ ^ 2 + (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), X t - xs⟫_ℝ
              + s / 2 * ‖gradient f (X t)‖ ^ 2) := by sorry

end HighResODE.NAGSCODE
