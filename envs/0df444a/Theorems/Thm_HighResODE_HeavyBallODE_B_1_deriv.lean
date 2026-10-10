-- Prove2me | Theorems.Thm_HighResODE_HeavyBallODE_B_1_deriv
-- name    : HighResODE.HeavyBallODE.B_1_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:53.407401+00:00
-- url     : https://prove2.me/theorems/8699f776-1162-4f02-a3d6-e7747f79a722
-- title:
--   App. B.1, p. 50 — along (1.10), dE/dt = −√μ[‖Ẋ‖² + (1 + √(μs))⟨∇f(X), X − x⋆⟩]
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$, let $s>0$, let $x_0,x^\star\in\mathbb R^n$, and let $(X,\dot X)$ be a solution of the high-resolution heavy-ball ODE (1.10),
--   $$\ddot X+2\sqrt\mu\,\dot X+\bigl(1+\sqrt{\mu s}\bigr)\nabla f(X)=0,\qquad X(0)=x_0,\ \dot X(0)=-\frac{2\sqrt s\,\nabla f(x_0)}{1+\sqrt{\mu s}},$$
--   on $[0,\infty)$. Let $\mathcal E$ be the Lyapunov function (3.3). Then for every $t\ge0$ the function $\mathcal E$ is differentiable at $t$ (from the right at $t=0$), with
--   $$\begin{aligned}\frac{d\mathcal E}{dt}&=\bigl(1+\sqrt{\mu s}\bigr)\langle\nabla f(X),\dot X\rangle+\frac12\bigl\langle\dot X,-2\sqrt\mu\,\dot X-(1+\sqrt{\mu s})\nabla f(X)\bigr\rangle\\&\qquad+\frac12\bigl\langle\dot X+2\sqrt\mu(X-x^\star),-(1+\sqrt{\mu s})\nabla f(X)\bigr\rangle\\&=-\sqrt\mu\Bigl[\|\dot X\|^2+\bigl(1+\sqrt{\mu s}\bigr)\langle\nabla f(X),X-x^\star\rangle\Bigr],\end{aligned}$$
--   where $X=X(t)$ and $\dot X=\dot X(t)$.
--
--   This exact derivative identity is the first step of the proof of Lemma 3.2; strong convexity is applied to it afterwards.
--
--   **Formalization Note.** The derivative is a derivative within $[0,\infty)$, and the statement asserts both that $\mathcal E$ has the first expression as its derivative and that the first expression equals the second. The identity uses only the differentiability of $f$ and the ODE; $x^\star$ is an arbitrary point here.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 50, App. B.1 (proof of Lemma 3.2), derivative display

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

namespace HighResODE.HeavyBallODE

open scoped InnerProductSpace

theorem B_1_deriv {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L) (hs : 0 < s)
    (xs x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n) (hsol : IsHeavyBallODE f μ s x0 X V) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (lyap f μ s xs X V)
        ((1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), V t⟫_ℝ
          + 1 / 2 * ⟪V t, -(2 * Real.sqrt μ) • V t - (1 + Real.sqrt (μ * s)) • gradient f (X t)⟫_ℝ
          + 1 / 2 * ⟪V t + (2 * Real.sqrt μ) • (X t - xs),
              -((1 + Real.sqrt (μ * s)) • gradient f (X t))⟫_ℝ)
        (Set.Ici 0) t ∧
      (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), V t⟫_ℝ
          + 1 / 2 * ⟪V t, -(2 * Real.sqrt μ) • V t - (1 + Real.sqrt (μ * s)) • gradient f (X t)⟫_ℝ
          + 1 / 2 * ⟪V t + (2 * Real.sqrt μ) • (X t - xs),
              -((1 + Real.sqrt (μ * s)) • gradient f (X t))⟫_ℝ
        = -(Real.sqrt μ) *
            (‖V t‖ ^ 2 + (1 + Real.sqrt (μ * s)) * ⟪gradient f (X t), X t - xs⟫_ℝ) := by sorry

end HighResODE.HeavyBallODE
