-- Prove2me | Theorems.Thm_NecoaraNG_ErrBound_descent_28
-- name    : NecoaraNG.ErrBound.descent_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:50.828772+00:00
-- url     : https://prove2.me/theorems/3ffc1341-e670-4295-ba4e-a33445e8b9c6
-- title:
--   (28), proof of Theorem 5, p. 10 — a projected gradient step decreases f by L_f/2 ‖x⁺ − x‖²
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, and let $f$ be convex on $X$, differentiable at every point of $X$, with gradient Lipschitz continuous on $X$ with constant $L_f>0$:
--   $\|\nabla f(x)-\nabla f(y)\|\le L_f\|x-y\|$ for all $x,y\in X$. Assume problem (P) has an optimal solution. For $x\in X$ let $x^+=[x-\tfrac1{L_f}\nabla f(x)]_X$ be the projected gradient step. Then
--   $$
--   f(x^+)\ \le\ f(x)-\frac{L_f}{2}\,\|x^+-x\|^2 .
--   $$
--
--   This sufficient-decrease inequality is the basic one-step estimate of the projected gradient method; in the paper it is used for Theorem 5 and Theorem 6 and throughout the convergence analysis.
--
--   **Formalization Note** The standing assumptions of p. 3 are stated as hypotheses (convexity of $f$ and the existence of an optimal point are among them, although this inequality does not need them). $x^+$ is any nearest point of $x-\tfrac1{L_f}\nabla f(x)$ in $X$; such a point exists and is unique.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 10, proof of Theorem 5, (28)

import Mathlib
import Definitions.Def_NecoaraNG_ErrBound_Setting

open scoped InnerProductSpace

namespace NecoaraNG.ErrBound

theorem descent_28 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f) :
    ∀ x ∈ X, ∀ xp, IsPGStep X f Lf x xp → f xp ≤ f x - Lf / 2 * ‖xp - x‖ ^ 2 := by sorry

end NecoaraNG.ErrBound
