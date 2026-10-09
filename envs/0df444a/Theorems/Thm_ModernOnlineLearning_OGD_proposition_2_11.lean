-- Prove2me | Theorems.Thm_ModernOnlineLearning_OGD_proposition_2_11
-- name    : ModernOnlineLearning.OGD.proposition_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:25.323984+00:00
-- url     : https://prove2.me/theorems/7af4badf-8277-4f69-a396-2cd608e67ae8
-- title:
--   Proposition 2.11 — projection decreases distance to feasible points
-- statement:
--   Let $V$ be a nonempty closed convex subset of a real inner-product space. If $p=\Pi_V(x)$ is a nearest point of $V$ to $x$, then every $y\in V$ satisfies
--   $$\|p-y\|\le\|x-y\|.$$
--
--   This projection inequality is the geometric step behind the one-round regret estimate. The nearest-point predicate records both $p\in V$ and its distance minimality.
-- source:
--   Orabona, arXiv:1912.13213v10, Proposition 2.11, p. 12

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

namespace ModernOnlineLearning.OGD

/-- Orabona, Proposition 2.11, p. 12: a metric projection onto a nonempty closed
convex set cannot increase the distance to any point of the set. -/
theorem proposition_2_11 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V) (x p y : E) (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection V x p)
    (hy : y ∈ V) : ‖p - y‖ ≤ ‖x - y‖ := by sorry

end ModernOnlineLearning.OGD
