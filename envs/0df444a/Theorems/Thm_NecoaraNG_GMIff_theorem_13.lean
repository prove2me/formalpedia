-- Prove2me | Theorems.Thm_NecoaraNG_GMIff_theorem_13
-- name    : NecoaraNG.GMIff.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:39.505237+00:00
-- url     : https://prove2.me/theorems/64fa2b4d-eb39-4f5a-a558-a66464de2f7c
-- title:
--   Theorem 13, p. 23 — the projected gradient step contracts dist(·, X*) if and only if f has quadratic functional growth (22)
-- statement:
--   Let problem (P), $\min_{x \in X} f(x)$, satisfy the standing assumptions: $X \subseteq \mathbb{R}^n$ is closed and convex, $f$ is convex and differentiable on $X$ with gradient Lipschitz on $X$ with constant $L_f > 0$, and the optimal set $X^*$ is nonempty. For $x \in X$ let $x^+ = [x - \tfrac{1}{L_f}\nabla f(x)]_X$ be one step of the gradient method (GM) with constant step size $1/L_f$, and let $\bar x = [x]_{X^*}$, $\bar x^+ = [x^+]_{X^*}$. Then:
--
--   1. **(Growth ⇒ linear convergence.)** If $f$ satisfies the quadratic functional growth (22) with some constant $\kappa_f > 0$, then, with $\mu_f = \kappa_f / L_f$,
--   $$\|x^+ - \bar x^+\|^2 \le \frac{1}{1 + \mu_f}\,\|x - \bar x\|^2 \qquad \forall x \in X .$$
--   2. **(Linear convergence ⇒ growth.)** If for some $\beta$ with $0 < \beta < 1$
--   $$\|x^+ - \bar x^+\| \le \beta\,\|x - \bar x\| \qquad \forall x \in X ,$$
--   then $f$ satisfies (22) with constant $L_f(1-\beta)^2$, i.e. $f$ belongs to $\mathcal F_{L_f, L_f(1-\beta)^2}$.
--
--   In particular, the gradient method with constant step size contracts the distance to the optimal set by a uniform factor $< 1$ at every feasible point if and only if $f$ has quadratic functional growth: quadratic functional growth is exactly the condition, among those studied in the paper, under which (GM) converges linearly.
--
--   **Formalization Note** The page does not define "converging linearly"; its proof identifies it with the one-step contraction of Theorem 5 (part 2, obtained from Theorem 5) and obtains that contraction from (52) at $\alpha_k = 1/L_f$ (part 1, in the squared form of (52)). Part 1 gives the contraction of part 2 with $\beta = (1+\mu_f)^{-1/2} \in (0,1)$, so the two parts together give the equivalence of Theorem 13. A multi-step notion ("$\operatorname{dist}(x^k, X^*) \le C q^k$ along every run") is not used: the converse for it is not what the page proves. Nearest points are predicates; they exist and are unique on the nonempty closed convex sets $X$ and $X^*$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 23, Theorem 13 (with Theorem 5, p. 9, and (52), p. 22)

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

namespace NecoaraNG.GMIff

theorem theorem_13 (n : ℕ) (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f) :
    (∀ κ : ℝ, 0 < κ → NecoaraNG.Chain.QuadFunGrowth X f κ →
      ∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar → ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp →
        ∀ xpbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp xpbar →
          ‖xp - xpbar‖ ^ 2 ≤ 1 / (1 + κ / Lf) * ‖x - xbar‖ ^ 2)
    ∧
    (∀ β : ℝ, 0 < β → β < 1 →
      (∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar → ∀ xp, NecoaraNG.ErrBound.IsPGStep X f Lf x xp →
        ∀ xpbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp xpbar → ‖xp - xpbar‖ ≤ β * ‖x - xbar‖) →
      NecoaraNG.Chain.QuadFunGrowth X f (Lf * (1 - β) ^ 2)) := by sorry

end NecoaraNG.GMIff
