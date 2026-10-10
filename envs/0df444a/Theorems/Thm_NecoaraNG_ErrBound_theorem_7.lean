-- Prove2me | Theorems.Thm_NecoaraNG_ErrBound_theorem_7
-- name    : NecoaraNG.ErrBound.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:52.961407+00:00
-- url     : https://prove2.me/theorems/ce32dcb4-137c-4387-9f8c-77257cd07103
-- title:
--   Theorem 7, p. 11 — quadratic functional growth (22) with κ_f implies the global error bound (31) with κ_f/(1 + μ_f + √(1 + μ_f))
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, and let $f$ be convex on $X$, differentiable at every point of $X$, with gradient Lipschitz continuous on $X$ with constant $L_f>0$, and assume problem (P) $\min_{x\in X}f(x)$ has an optimal solution, so that the optimal set $X^*$ is nonempty. Suppose $f$ has **quadratic functional growth** with constant $\kappa_f>0$: for all $x\in X$ and $\bar x=[x]_{X^*}$,
--   $$
--   f(x)-f^*\ \ge\ \frac{\kappa_f}{2}\|x-\bar x\|^2. \tag{22}
--   $$
--   Let $\mu_f=\kappa_f/L_f$. Then $f$ satisfies the **global error bound** with constant $\frac{1}{1+\mu_f+\sqrt{1+\mu_f}}\cdot\kappa_f$: for all $x\in X$, with $\bar x=[x]_{X^*}$, $x^+=[x-\tfrac1{L_f}\nabla f(x)]_X$ and gradient mapping $g(x)=L_f(x-x^+)$,
--   $$
--   \|g(x)\|\ \ge\ \frac{1}{1+\mu_f+\sqrt{1+\mu_f}}\cdot\kappa_f\ \|x-\bar x\|. \tag{31}
--   $$
--   Equivalently, $\mathcal F_{L_f,\kappa_f}(X)\subseteq\mathcal E_{L_f,\frac{1}{1+\mu_f+\sqrt{1+\mu_f}}\kappa_f}(X)$ (34).
--
--   Together with Theorem 6 (the converse direction, with constant $\mu_f\kappa_f$) this shows that, for convex functions with Lipschitz gradient on a closed convex set, quadratic functional growth and the error bound in terms of the gradient mapping are equivalent up to constants depending only on $\mu_f$. Linear convergence of projected gradient methods can therefore be derived from either condition.
--
--   **Formalization Note** The constant is written $\kappa/(1+\kappa/L_f+\sqrt{1+\kappa/L_f})$, the same number as the paper's $\frac{1}{1+\mu_f+\sqrt{1+\mu_f}}\cdot\kappa_f$. The error bound uses the gradient mapping $g(x)=L_f(x-x^+)$, not $\nabla f(x)$. The projections $\bar x$ and $x^+$ are characterized as nearest points; the statement quantifies over every such point (they are unique). The paper's "simple" set (cheap projection) is not a mathematical hypothesis and is dropped; "closed convex function" is covered by $f$ being real-valued, convex and differentiable on $X$. $f$ is a function on all of $\mathbb R^n$ whose values off $X$ play no role.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 11, Theorem 7, (34)

import Mathlib
import Definitions.Def_NecoaraNG_ErrBound_Setting

open scoped InnerProductSpace

namespace NecoaraNG.ErrBound

theorem theorem_7 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ) :
    ErrorBound X f Lf (κ / (1 + κ / Lf + Real.sqrt (1 + κ / Lf))) := by sorry

end NecoaraNG.ErrBound
