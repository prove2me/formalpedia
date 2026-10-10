-- Prove2me | Theorems.Thm_NecoaraNG_ErrBound_theorem_7_step_1
-- name    : NecoaraNG.ErrBound.theorem_7_step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:58.127548+00:00
-- url     : https://prove2.me/theorems/e977c98b-778d-4563-97d8-75313ae11cc0
-- title:
--   Proof of Theorem 7, first display chain, p. 11 — ⟨g(x), x⁺ − x̄⁺⟩ + ‖g(x)‖²/(2L_f) ≥ f(x⁺) − f* ≥ κ_f/2 ‖x⁺ − x̄⁺‖²
-- statement:
--   Under the standing assumptions of problem (P) ($X\subseteq\mathbb R^n$ closed and convex, $f$ convex on $X$ and differentiable at every point of $X$, $\nabla f$ Lipschitz on $X$ with constant $L_f>0$, an optimal solution exists), suppose $f$ has quadratic functional growth (22) with constant $\kappa_f>0$. Let $x\in X$, let $x^+=[x-\tfrac1{L_f}\nabla f(x)]_X$, $g(x)=L_f(x-x^+)$, and let $\bar x^+=[x^+]_{X^*}$ be the nearest point of $x^+$ in the optimal set. Then
--   $$
--   \langle g(x),\,x^+-\bar x^+\rangle+\frac{1}{2L_f}\|g(x)\|^2\ \ge\ f(x^+)-f^*\ \ge\ \frac{\kappa_f}{2}\,\|x^+-\bar x^+\|^2 .
--   $$
--
--   This is the first step of the proof of Theorem 7: it combines the gradient-mapping inequality (29) at $y=\bar x^+$ with the growth condition (22) at the feasible point $x^+$.
--
--   **Formalization Note** The chain is stated as the conjunction of its two inequalities, with $f^*$ written $f(\bar x^+)$ (equal to $f^*$ since $\bar x^+\in X^*$).
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 11, proof of Theorem 7, first two displays

import Mathlib
import Definitions.Def_NecoaraNG_ErrBound_Setting

open scoped InnerProductSpace

namespace NecoaraNG.ErrBound

theorem theorem_7_step_1 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ) :
    ∀ x ∈ X, ∀ xp, IsPGStep X f Lf x xp → ∀ xpbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp xpbar →
      κ / 2 * ‖xp - xpbar‖ ^ 2 ≤ f xp - f xpbar ∧
      f xp - f xpbar ≤ ⟪Lf • (x - xp), xp - xpbar⟫_ℝ + 1 / (2 * Lf) * ‖Lf • (x - xp)‖ ^ 2 := by sorry

end NecoaraNG.ErrBound
