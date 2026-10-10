-- Prove2me | Theorems.Thm_NecoaraNG_Chain_theorem_1
-- name    : NecoaraNG.Chain.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:03.115999+00:00
-- url     : https://prove2.me/theorems/e6161da1-b45c-4553-9e13-1a9813d2d789
-- title:
--   Theorem 1, p. 6 — quasi-strong convexity (10) implies quadratic under-approximation (13) with the same κ
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f$ be convex on $X$, differentiable at every point of $X$, with $L_f$-Lipschitz gradient on $X$ ($L_f>0$), and assume the optimal set $X^*=\arg\min_{x\in X}f(x)$ is nonempty. Let $\kappa>0$, and write $\bar x=[x]_{X^*}$ for a nearest point of $X^*$ to $x$ and $f^*$ for the optimal value. If
--   $$f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2\qquad\forall x\in X,$$
--   then
--   $$f(x)\ge f^*+\langle\nabla f(\bar x),x-\bar x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2\qquad\forall x\in X.$$
--
--   In class notation: $q\mathcal S_{L_f,\kappa}(X)\subseteq\mathcal U_{L_f,\kappa}(X)$ (14). Convexity of $f$ is essential: (10) alone does not even imply convexity.
--
--   **Formalization Note** $f^*$ is written $f(\bar x)$; both inequalities are required for every nearest point $\bar x$ (which is unique here).
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 6, Theorem 1, (14)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.Chain

open scoped InnerProductSpace

/-- Theorem 1, p. 6: inequality (10) implies inequality (13), with the same constant `κ`. -/
theorem theorem_1 {n : ℕ} (X : Set (E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : E n) (hxstar : xstar ∈ optSet X f) (κ : ℝ) (hκ : 0 < κ) :
    QuasiStrong X f κ → QuadUnder X f κ := by sorry

end NecoaraNG.Chain
