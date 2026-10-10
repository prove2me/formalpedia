-- Prove2me | Theorems.Thm_NecoaraNG_GMIff_ineq_26
-- name    : NecoaraNG.GMIff.ineq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:48.677923+00:00
-- url     : https://prove2.me/theorems/05e72b2a-9be9-4186-8dcc-a17600e3c5f9
-- title:
--   (26), proof of Theorem 5, p. 10 — contraction of dist(·, X*) gives (1 − β)‖x − x̄‖ ≤ ‖x − x⁺‖
-- statement:
--   Under the standing assumptions of problem (P) ($X$ nonempty closed convex, $f$ convex with $L_f$-Lipschitz gradient (1) on $X$, $L_f > 0$, $X^* \ne \emptyset$), let $0 < \beta < 1$ and suppose that the projected gradient step contracts the distance to the optimal set:
--   $$\|x^+ - \bar x^+\| \le \beta \|x - \bar x\| \qquad \forall x \in X,$$
--   where $x^+ = [x - \tfrac{1}{L_f}\nabla f(x)]_X$, $\bar x = [x]_{X^*}$ and $\bar x^+ = [x^+]_{X^*}$. Then for every $x \in X$,
--   $$(1 - \beta)\|x - \bar x\| \le \|x - x^+\| .$$
--
--   The inequality turns the contraction hypothesis into a lower bound on the step length, which combined with (28) gives quadratic functional growth (Theorem 5).
--
--   **Formalization Note** The contraction hypothesis quantifies over all nearest points $\bar x$, $x^+$, $\bar x^+$; since they are unique this is the paper's hypothesis.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 10, proof of Theorem 5, (26)

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

namespace NecoaraNG.GMIff

theorem ineq_26 (n : ℕ) (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcontr : ∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar → ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp →
      ∀ xpbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp xpbar → ‖xp - xpbar‖ ≤ β * ‖x - xbar‖) :
    ∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar → ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp →
      (1 - β) * ‖x - xbar‖ ≤ ‖x - xp‖ := by sorry

end NecoaraNG.GMIff
