-- Prove2me | Theorems.Thm_NonsmoothNewton_Shared_exists_local_clarkeJac_control
-- name    : NonsmoothNewton.Shared.exists_local_clarkeJac_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T20:32:01.432029+00:00
-- url     : https://prove2.me/theorems/865917c2-8a2c-432b-a9ff-84c219220afc
-- title:
--   Local nonemptiness and uniform boundedness of Clarke's generalized Jacobian
-- statement:
--   Let $F : E \to G$ be locally Lipschitz at a point $x$, where $E$ and $G$ are finite-dimensional real normed spaces. Then there are a constant $K \ge 0$ and a radius $r > 0$ such that for every $y$ in the open ball of radius $r$ around $x$, Clarke's generalized Jacobian $\partial F(y) = \operatorname{co}\{\partial_B F(y)\}$ is nonempty and every one of its elements has operator norm at most $K$.
--
--   **Formalization Note** `clarkeJac F y` is `convexHull ℝ (bJac F y)`. Nonemptiness is immediate from nonemptiness of `bJac F y` since a subset lies in its own convex hull. The uniform bound passes from the B-limit set to its convex hull because a closed ball of radius $K$ in the operator-normed space of continuous linear maps is convex and closed, and a convex hull of a set contained in a closed convex set stays inside it. This is the aggregate statement that the generalized Jacobians $\partial F$ remain nonempty and uniformly bounded near a point.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 354, Eq. (2.1). Aggregates the local B-limit control of exists_local_bJac_control through the convex hull.

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set

namespace NonsmoothNewton.Shared

/-- Local control of Clarke's generalized Jacobian `clarkeJac F y` of Qi–Sun (1993),
Eq. (2.1), p. 354. If `F : E → G` is locally Lipschitz at `x` and `E`, `G` are
finite-dimensional real normed spaces, then there are a constant `K` and a radius
`r > 0` such that `clarkeJac F y` is nonempty for every `y` in the open ball of radius
`r` about `x`, and every element of `clarkeJac F y` has operator norm at most `K`.

This is the aggregate form of the local B-limit control: since
`clarkeJac F y = convexHull ℝ (bJac F y)` and a closed ball of radius `K` is convex,
nonemptiness and uniform boundedness pass from the B-limit sets to the
generalized Jacobian. -/
theorem exists_local_clarkeJac_control {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    ∃ K : NNReal, ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ Metric.ball x r, (clarkeJac F y).Nonempty) ∧
      (∀ y ∈ Metric.ball x r,
        ∀ V ∈ clarkeJac F y, ‖V‖ ≤ (K : ℝ)) := by sorry

end NonsmoothNewton.Shared
