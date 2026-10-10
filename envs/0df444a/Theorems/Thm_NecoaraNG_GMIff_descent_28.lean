-- Prove2me | Theorems.Thm_NecoaraNG_GMIff_descent_28
-- name    : NecoaraNG.GMIff.descent_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:31.657825+00:00
-- url     : https://prove2.me/theorems/593357b7-ddef-4ce2-8e08-5732195bd615
-- title:
--   (28), proof of Theorem 5, p. 10 — f(x⁺) ≤ f(x) − (L_f/2)‖x⁺ − x‖²
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be a nonempty closed convex set and $f$ a convex function, differentiable at every point of $X$, whose gradient is Lipschitz on $X$ with constant $L_f > 0$:
--   $$\|\nabla f(x) - \nabla f(y)\| \le L_f \|x - y\| \qquad \forall x, y \in X, \tag{1}$$
--   and assume the optimal set $X^*$ of $\min_{x \in X} f(x)$ is nonempty. For $x \in X$ let $x^+ = [x - \tfrac{1}{L_f}\nabla f(x)]_X$ be the projected gradient step. Then
--   $$f(x^+) \le f(x) - \frac{L_f}{2}\|x^+ - x\|^2 .$$
--
--   This sufficient-decrease inequality is one of the two ingredients of Theorem 5: a projected gradient step decreases $f$ by an amount proportional to the squared step length.
--
--   **Formalization Note** The standing assumptions of the paper (p. 3) are kept as hypotheses; convexity of $f$ and nonemptiness of $X^*$ are not used by this inequality. $f$ is defined on all of $\mathbb{R}^n$, but only its values and gradient at points of $X$ enter.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 10, proof of Theorem 5, (27)–(28)

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

namespace NecoaraNG.GMIff

theorem descent_28 (n : ℕ) (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f) :
    ∀ x ∈ X, ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp → f xp ≤ f x - Lf / 2 * ‖xp - x‖ ^ 2 := by sorry

end NecoaraNG.GMIff
