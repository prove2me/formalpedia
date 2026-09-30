-- Prove2me | Theorems.Thm_KellyStochasticNetworks_wardrop_from_minimizer
-- name    : KellyStochasticNetworks.wardrop_from_minimizer
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:59:37.218759+00:00
-- url     : https://prove2.me/theorems/bf2b1157-c460-4de3-8484-da2b072a2dc3
-- title:
--   A minimizer of $\sum_j \int_0^{y_j} D_j$ is a Wardrop equilibrium
-- statement:
--   Consider the convex program in the proof of Theorem 4.3:
--   $$\text{minimize}\quad \sum_j \int_0^{y_j} D_j(u)\,du \qquad\text{over feasible route flows }
--     x \ge 0 \text{ with } Hx = f, \quad y = Ax .$$
--   If $x$ is feasible and minimizes this objective over the feasible set, then $x$ is a Wardrop
--   equilibrium: every route carrying positive traffic has minimal delay among the routes serving
--   the same source–destination pair.
--
--   This is the half of the book's one-to-one correspondence that delivers Theorem 4.3, since the
--   feasible region is convex and compact and the objective is continuous, so a minimizer exists.
--   The mechanism is the first-order conditions: differentiating in $y_j$ identifies the
--   multiplier $\mu_j$ with the link delay $D_j(y_j)$, and differentiating in $x_r$ gives that the
--   multiplier $\lambda_{s(r)}$ equals the route delay $\sum_j \mu_j A_{jr}$ on routes carrying
--   traffic and is a lower bound on the others. Read back, $\lambda_{s(r)}$ is the minimal delay
--   available to the source–destination pair, which is Definition 4.2.
--
--   It is worth being clear about what is *not* being minimized. The objective is
--   $\sum_j\int_0^{y_j}D_j$, not the total delay $\sum_j y_jD_j(y_j)$ that a planner would want to
--   minimize. Braess's paradox is exactly the gap between the two.
--
--   **Formalization Note** Minimality is stated directly as the defining inequality over the
--   feasible set, so no optimization API is presupposed. The incidence matrix is constrained to
--   have entries $0$ or $1$, as in the book's definition for this chapter, and the delay functions
--   are continuous and increasing in the weak sense.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 97 (PDF p. 105), the proof of Theorem 4.3: 'Consider the optimization problem minimize sum_{j} int_0^{y_j} D_j(u) du subject to Hx = f, Ax = y, over x >= 0, y. ... at the minimum the derivative with respect to y_j is equal to 0, i.e. we can identify mu_j = D_j(y_j) as the delay on link j. The derivative with respect to x_r must be non-negative, and 0 if x_r > 0, so lambda_{s(r)} = sum_j mu_j A_{jr} if x_r > 0, <= sum_j mu_j A_{jr} if x_r = 0. Therefore, we can interpret lambda_{s(r)} as the minimal delay available to the source-destination pair s(r). Consequently, solutions of this optimization problem are in one-to-one correspondence with Wardrop equilibria.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem wardrop_from_minimizer {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hD : ∀ j, Continuous (D j)) (hmono : ∀ j, Monotone (D j))
    (x : Fin R → ℝ) (hx : x ∈ wardropFeasible s f)
    (hmin : ∀ z ∈ wardropFeasible s f, wardropObjective A D x ≤ wardropObjective A D z) :
    IsWardropEquilibrium A s D f x := by sorry

end KellyStochasticNetworks
