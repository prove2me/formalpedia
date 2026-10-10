-- Prove2me | Theorems.Thm_NecoaraNG_ErrBound_gradient_mapping_29
-- name    : NecoaraNG.ErrBound.gradient_mapping_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:02.386273+00:00
-- url     : https://prove2.me/theorems/2aad25e3-6710-460b-90c6-8ea9782847d7
-- title:
--   (29), p. 10 — main inequality of the gradient mapping: f(y) ≥ f(x⁺) + ⟨g(x), y − x⟩ + ‖g(x)‖²/(2L_f)
-- statement:
--   Under the standing assumptions of problem (P) — $X\subseteq\mathbb R^n$ closed and convex, $f$ convex on $X$ and differentiable at every point of $X$, $\nabla f$ Lipschitz on $X$ with constant $L_f>0$, and an optimal solution exists — let $x\in X$, let $x^+=[x-\tfrac1{L_f}\nabla f(x)]_X$ be the projected gradient step and $g(x)=L_f(x-x^+)$ the gradient mapping. Then for every $y\in X$,
--   $$
--   f(y)\ \ge\ f(x^+)+\langle g(x),\,y-x\rangle+\frac{1}{2L_f}\,\|g(x)\|^2 .
--   $$
--
--   This is the main property of the gradient mapping for convex functions with Lipschitz continuous gradient (Nesterov, *Introductory Lectures on Convex Optimization*, Theorem 2.2.7). Evaluated at suitable points of $X^*$ it drives the comparison between quadratic functional growth and the error bound.
--
--   **Formalization Note** The paper states (29) for all $x\in\mathbb R^n$. Under its standing assumptions $f$ is only given on $X$, so $\nabla f(x)$, and hence (29), only make sense for $x\in X$; the statement is restricted to $x\in X$, which is all that Theorem 7 uses. No hypothesis on $f$ outside $X$ is added.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 10, (29) (citing Nesterov, Theorem 2.2.7)

import Mathlib
import Definitions.Def_NecoaraNG_ErrBound_Setting

open scoped InnerProductSpace

namespace NecoaraNG.ErrBound

theorem gradient_mapping_29 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f) :
    ∀ x ∈ X, ∀ xp, IsPGStep X f Lf x xp → ∀ y ∈ X,
      f xp + ⟪Lf • (x - xp), y - x⟫_ℝ + 1 / (2 * Lf) * ‖Lf • (x - xp)‖ ^ 2 ≤ f y := by sorry

end NecoaraNG.ErrBound
