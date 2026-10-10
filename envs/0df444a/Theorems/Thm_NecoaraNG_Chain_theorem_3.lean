-- Prove2me | Theorems.Thm_NecoaraNG_Chain_theorem_3
-- name    : NecoaraNG.Chain.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:46:59.977597+00:00
-- url     : https://prove2.me/theorems/d0a0985f-ddd4-4e86-9903-59e1cf07d4e5
-- title:
--   Theorem 3, p. 8 — quadratic gradient growth (17) implies quadratic under-approximation (13) with the same κ
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f$ be convex on $X$, differentiable at every point of $X$, with $L_f$-Lipschitz gradient on $X$ ($L_f>0$), and assume the optimal set $X^*=\arg\min_{x\in X}f(x)$ is nonempty. Let $\kappa>0$ and let $\bar x=[x]_{X^*}$. If
--   $$\langle\nabla f(x)-\nabla f(\bar x),x-\bar x\rangle\ge\kappa\|x-\bar x\|^2\qquad\forall x\in X,$$
--   then
--   $$f(x)\ge f^*+\langle\nabla f(\bar x),x-\bar x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2\qquad\forall x\in X.$$
--
--   In class notation: $\mathcal G_{L_f,\kappa}(X)\subseteq\mathcal U_{L_f,\kappa}(X)$ (21).
--
--   **Formalization Note** $f^*$ is written $f(\bar x)$; both inequalities are required for every nearest point $\bar x$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 8, Theorem 3, (21)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.Chain

open scoped InnerProductSpace

/-- Theorem 3, p. 8: inequality (17) implies inequality (13), with the same constant `κ`. -/
theorem theorem_3 {n : ℕ} (X : Set (E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : E n) (hxstar : xstar ∈ optSet X f) (κ : ℝ) (hκ : 0 < κ) :
    QuadGradGrowth X f κ → QuadUnder X f κ := by sorry

end NecoaraNG.Chain
