-- Prove2me | Theorems.Thm_NonsmoothNewton_Shared_exists_local_bJac_control
-- name    : NonsmoothNewton.Shared.exists_local_bJac_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T19:44:06.496986+00:00
-- url     : https://prove2.me/theorems/2ad3cd7b-ecea-45df-8c4e-0da2b841091e
-- title:
--   Local nonemptiness and uniform boundedness of the B-Jacobian of a locally Lipschitz map
-- statement:
--   Let $F : E \to G$ be locally Lipschitz at a point $x$, where $E$ and $G$ are finite-dimensional real normed spaces. Then there are a constant $K \ge 0$ and a radius $r > 0$ such that (i) $F$ is $K$-Lipschitz on the closed ball of radius $r$ around $x$; (ii) for every $y$ in the open ball of radius $r$, the B-limit set $\partial_B F(y)$ is nonempty; and (iii) for every $y$ in that open ball and every $V \in \partial_B F(y)$, the operator norm of $V$ is at most $K$.
--
--   **Formalization Note** $\partial_B F(y)$ is `bJac F y`, the set of limits of the Fréchet derivatives `fderiv ℝ F` along sequences of differentiability points converging to $y$. Nonemptiness is Rademacher's theorem (differentiability almost everywhere on the closed ball, hence a dense set of differentiability points) together with Bolzano–Weierstrass in the finite-dimensional space of continuous linear maps. The norm bound is the mean value inequality: a $K$-Lipschitz map has derivative of norm at most $K$ at each of its differentiability points.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 354, Eq. (2.1) and Section 3. Uses Rademacher's theorem and the mean value inequality (sharp converse).

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set

namespace NonsmoothNewton.Shared

/-- Local control of the B-limit set `bJac F y` of Qi–Sun (1993), Eq. (2.1), p. 354.
If `F : E → G` is locally Lipschitz at `x` and `E`, `G` are finite-dimensional real
normed spaces, then there are a constant `K` and a radius `r > 0` such that `F` is
`K`-Lipschitz on the closed ball of radius `r` about `x`, the B-limit set `bJac F y` is
nonempty for every `y` in the open ball, and every element of `bJac F y` has operator
norm at most `K`.

This is the analytic input that makes the B-limit sets and hence Clarke's generalized
Jacobian `convexHull ℝ (bJac F y)` locally nondegenerate: a compact, uniformly
bounded family of candidate Jacobians. -/
theorem exists_local_bJac_control {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    ∃ K : NNReal, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith K F (Metric.closedBall x r) ∧
      (∀ y ∈ Metric.ball x r, (bJac F y).Nonempty) ∧
      (∀ y ∈ Metric.ball x r,
        ∀ V ∈ bJac F y, ‖V‖ ≤ (K : ℝ)) := by sorry

end NonsmoothNewton.Shared
