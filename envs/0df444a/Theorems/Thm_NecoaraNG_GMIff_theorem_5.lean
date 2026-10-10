-- Prove2me | Theorems.Thm_NecoaraNG_GMIff_theorem_5
-- name    : NecoaraNG.GMIff.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:22.039754+00:00
-- url     : https://prove2.me/theorems/1fd8ecf4-d44b-41c6-9b85-a28bf82a51cc
-- title:
--   Theorem 5, p. 9 — a β-contraction of the projected gradient step gives quadratic functional growth with κ_f = L_f(1 − β)²
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be closed and convex, and let $f$ be a convex function with Lipschitz continuous gradient with constant $L_f > 0$ on $X$, whose optimal set $X^*$ over $X$ is nonempty. For $x \in X$ write $x^+ = [x - \tfrac{1}{L_f}\nabla f(x)]_X$, $\bar x = [x]_{X^*}$ and $\bar x^+ = [x^+]_{X^*}$. If there is a constant $\beta$ with $0 < \beta < 1$ such that
--   $$\|x^+ - \bar x^+\| \le \beta \|x - \bar x\| \qquad \forall x \in X,$$
--   then $f$ satisfies the quadratic functional growth (22) on $X$ with constant $\kappa_f = L_f(1 - \beta)^2$:
--   $$f(x) - f^* \ge \frac{L_f(1-\beta)^2}{2}\|x - \bar x\|^2 \qquad \forall x \in X.$$
--
--   This is the "only if" half of Theorem 13: if one projected gradient step with step size $1/L_f$ brings every feasible point linearly closer to the optimal set, then $f$ must grow quadratically away from $X^*$.
--
--   **Formalization Note** The contraction hypothesis is stated for every choice of the nearest points $\bar x$, $x^+$, $\bar x^+$, which are unique on nonempty closed convex sets. $f^*$ is $f(\bar x)$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 9, Theorem 5

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

namespace NecoaraNG.GMIff

theorem theorem_5 (n : ℕ) (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcontr : ∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar → ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp →
      ∀ xpbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp xpbar → ‖xp - xpbar‖ ≤ β * ‖x - xbar‖) :
    NecoaraNG.Chain.QuadFunGrowth X f (Lf * (1 - β) ^ 2) := by sorry

end NecoaraNG.GMIff
