-- Prove2me | Theorems.Thm_HighResODE_NAGSCODE_lemma_3_1
-- name    : HighResODE.NAGSCODE.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:23.83404+00:00
-- url     : https://prove2.me/theorems/4319a333-21ef-4d94-9d90-3d408af8b160
-- title:
--   Lemma 3.1, p. 13 — along the NAG-SC high-resolution ODE, dE/dt ≤ −(√μ/4)E − (√s/2)[‖∇f(X)‖² + Ẋᵀ∇²f(X)Ẋ] for every s > 0
-- statement:
--   Let $f\in\mathcal S^2_{\mu,L}(\mathbb R^n)$ with minimizer $x^\star$ and let $s>0$ be any step size. Let $X=X(t)$ be the solution of the high-resolution ODE of NAG-SC
--   $$\ddot X+2\sqrt\mu\,\dot X+\sqrt s\,\nabla^2 f(X)\dot X+\big(1+\sqrt{\mu s}\big)\nabla f(X)=0,\qquad X(0)=x_0,\ \dot X(0)=-\frac{2\sqrt s\,\nabla f(x_0)}{1+\sqrt{\mu s}},$$
--   and let $\mathcal E$ be the Lyapunov function (2.4). Then for every $t\ge0$,
--   $$\frac{d\mathcal E(t)}{dt}\le-\frac{\sqrt\mu}{4}\mathcal E(t)-\frac{\sqrt s}{2}\Big[\|\nabla f(X(t))\|^2+\dot X(t)^\top\nabla^2 f(X(t))\dot X(t)\Big].\tag{3.1}$$
--
--   The bracket is nonnegative for convex $f$, so the lemma gives $\dot{\mathcal E}\le-\frac{\sqrt\mu}{4}\mathcal E$, the differential inequality from which Theorem 1 follows; the bracket itself is what the discretization of §3.2 exploits.
--
--   **Formalization Note.** The derivative is one-sided within $[0,\infty)$ (from the right at $t=0$) and is stated as the existence of a number that is the derivative and satisfies (3.1). The solution is any pair $(X,V)$ satisfying the ODE and the initial conditions; existence and uniqueness (Proposition 2.1) are not assumed, so "the solution" is read as "every solution". $\nabla^2 f(X)\dot X$ is the Fréchet derivative of $\nabla f$ at $X$ applied to $\dot X$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 13, Lemma 3.1, (3.1)

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

open scoped InnerProductSpace

namespace HighResODE.NAGSCODE

theorem lemma_3_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L s : ℝ) (hf : IsS2 f μ L)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xs ≤ f z) (hs : 0 < s)
    (x0 : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n))
    (hsol : IsNAGSCODE f μ s x0 X V) :
    ∀ t, 0 ≤ t → ∃ e' : ℝ, HasDerivWithinAt (lyap f μ s xs X V) e' (Set.Ici 0) t ∧
      e' ≤ -(Real.sqrt μ / 4) * lyap f μ s xs X V t
        - Real.sqrt s / 2 * (‖gradient f (X t)‖ ^ 2
          + ⟪V t, fderiv ℝ (gradient f) (X t) (V t)⟫_ℝ) := by sorry

end HighResODE.NAGSCODE
