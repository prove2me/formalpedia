-- Prove2me | Theorems.Thm_NecoaraNG_Chain_theorem_2
-- name    : NecoaraNG.Chain.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:46:52.452995+00:00
-- url     : https://prove2.me/theorems/ce946e1f-457f-40e6-a6a6-f2ada6664e4b
-- title:
--   Theorem 2, p. 7 — quasi-strong convexity (10) implies quadratic gradient growth (17) with the same κ
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f$ be convex on $X$, differentiable at every point of $X$, with $L_f$-Lipschitz gradient on $X$ ($L_f>0$), and assume the optimal set $X^*=\arg\min_{x\in X}f(x)$ is nonempty. Let $\kappa>0$ and let $\bar x=[x]_{X^*}$. If $f$ is quasi-strongly convex with constant $\kappa$,
--   $$f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2\qquad\forall x\in X,$$
--   then $f$ has quadratic gradient growth with the same constant:
--   $$\langle\nabla f(x)-\nabla f(\bar x),x-\bar x\rangle\ge\kappa\|x-\bar x\|^2\qquad\forall x\in X.$$
--
--   In class notation: $q\mathcal S_{L_f,\kappa}(X)\subseteq\mathcal G_{L_f,\kappa}(X)$ (18).
--
--   **Formalization Note** $f^*$ is written $f(\bar x)$; both inequalities are required for every nearest point $\bar x$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 7, Theorem 2, (18)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.Chain

open scoped InnerProductSpace

/-- Theorem 2, p. 7: inequality (10) implies inequality (17), with the same constant `κ`. -/
theorem theorem_2 {n : ℕ} (X : Set (E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : E n) (hxstar : xstar ∈ optSet X f) (κ : ℝ) (hκ : 0 < κ) :
    QuasiStrong X f κ → QuadGradGrowth X f κ := by sorry

end NecoaraNG.Chain
