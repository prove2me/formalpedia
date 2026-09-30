-- Prove2me | Theorems.Thm_KellyStochasticNetworks_wardrop_objective_convex
-- name    : KellyStochasticNetworks.wardrop_objective_convex
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:59:09.00708+00:00
-- url     : https://prove2.me/theorems/60588969-ad8f-472e-b19b-da775d860372
-- title:
--   The integral of an increasing delay function is convex
-- statement:
--   Let $D : \mathbb{R}\to\mathbb{R}$ be continuous and increasing. Then
--   $$y \;\longmapsto\; \int_0^{y} D(u)\,du$$
--   is a convex function on $\mathbb{R}$.
--
--   This is the analytic fact behind the proof of Theorem 4.3. The objective of the optimization
--   problem whose solutions are the Wardrop equilibria is $\sum_j \int_0^{y_j}D_j(u)\,du$; since
--   each link's delay function is increasing, each summand is convex in the link flow $y_j$, and
--   since $y = Ax$ is linear in the route flows the whole objective is convex in $x$. Convexity on
--   a compact feasible region is what delivers an optimum and lets the Lagrangian characterization
--   be read off.
--
--   Note what is *not* assumed: $D$ need not be convex, and the book explicitly declines to assume
--   it. Monotonicity alone gives convexity of the integral, because the integral's derivative is
--   $D$ itself.
--
--   **Formalization Note** "Increasing" is taken in the weak sense, so a delay function that is
--   flat on an interval is allowed; this is the weaker hypothesis and the one the argument needs.
--   Convexity is asserted on the whole real line rather than on the non-negative half, which is
--   where flows live; the stronger statement is true and avoids carrying a domain restriction
--   through the composition with $y = Ax$.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 97 (PDF p. 105), in the proof of Theorem 4.3: 'The feasible region is convex and compact, and the objective function is differentiable and convex (because D_j is an increasing, continuous function). Thus, an optimum exists and can be found by Lagrangian techniques.' The objective is sum_j int_0^{y_j} D_j(u) du. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem wardrop_objective_convex (D : ℝ → ℝ) (hD : Continuous D) (hmono : Monotone D) :
    ConvexOn ℝ Set.univ (fun y : ℝ => ∫ u in (0:ℝ)..y, D u) := by sorry

end KellyStochasticNetworks
