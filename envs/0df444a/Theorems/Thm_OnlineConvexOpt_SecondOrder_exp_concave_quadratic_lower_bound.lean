-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_exp_concave_quadratic_lower_bound
-- name    : OnlineConvexOpt.SecondOrder.exp_concave_quadratic_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:32:50.653398+00:00
-- url     : https://prove2.me/theorems/a65ad6eb-e420-4c29-ae25-b41eca18cadd
-- title:
--   Lemma 4.3 — the quadratic lower bound exp-concavity gives
-- statement:
--   Let $f : K \to \mathbb{R}$ be an $\alpha$-exp-concave function on a convex set $K$ in a real
--   inner-product space, let $D$ be the diameter of $K$, and let $G$ bound the norm of every
--   (sub)gradient of $f$ on $K$. Then for every
--   $$
--   \gamma \le \tfrac12 \min\Bigl\{\tfrac{1}{GD}, \alpha\Bigr\}
--   $$
--   and all $x, y \in K$, writing $g = \nabla f(y)$,
--   $$
--   f(x) \;\ge\; f(y) + g^\top (x - y) + \frac{\gamma}{2}\bigl(g^\top(x-y)\bigr)^2 .
--   $$
--   (The source states the quadratic term as $(x-y)^\top g g^\top (x-y)$; since $gg^\top$ has
--   rank one, this equals $(g^\top(x-y))^2$.) This inequality is the workhorse of the chapter:
--   it is a quadratic strengthening of the usual first-order convexity lower bound
--   $f(x) \ge f(y) + g^\top(x-y)$, and it is exactly what lets the online Newton step analysis
--   (Lemma 4.6) replace the linear regret bound of online gradient descent with a bound that
--   telescopes logarithmically.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 59, PDF p. 81, Lemma 4.3

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave

open OnlineConvexOpt.SecondOrder

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 4.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 59, PDF p. 81). Let `f : K → ℝ` be `α`-exp-concave, `D` the diameter of
`K` and `G` a bound on the (sub)gradients of `f` over `K` (`hG`, stated via `HasGradientAt` as
in `OnlineConvexOpt.FirstOrder`). Then for all `γ ≤ (1/2) min{1/(GD), α}` and all `x, y ∈ K`,
`f(x) ≥ f(y) + ∇f(y)^⊤(x - y) + (γ/2)(x - y)^⊤∇f(y)∇f(y)^⊤(x - y)`, where the quadratic term
`(x - y)^⊤∇f(y)∇f(y)^⊤(x - y)` equals `(∇f(y)^⊤(x - y))²` since `∇f(y)∇f(y)^⊤` has rank one. -/
theorem exp_concave_quadratic_lower_bound (α D G γ : ℝ) (K : Set E) (f : E → ℝ)
    (hf : IsExpConcaveOn α K f) (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ p ∈ K, ∀ v, HasGradientAt f v p → ‖v‖ ≤ G)
    (hγ : γ ≤ (1 / 2) * min (1 / (G * D)) α)
    (x y : E) (hx : x ∈ K) (hy : y ∈ K) (g : E) (hg : HasGradientAt f g y) :
    f y + inner ℝ g (x - y) + (γ / 2) * (inner ℝ g (x - y)) ^ 2 ≤ f x := by sorry

end OnlineConvexOpt.SecondOrder
