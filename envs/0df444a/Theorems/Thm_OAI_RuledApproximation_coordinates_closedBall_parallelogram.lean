-- Prove2me | Theorems.Thm_OAI_RuledApproximation_coordinates_closedBall_parallelogram
-- name    : OAI.RuledApproximation.coordinates_closedBall_parallelogram
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:42:16.990117+00:00
-- url     : https://prove2.me/theorems/b40471b4-a2a8-4f56-a25c-97d211922570
-- title:
--   Closed balls of the maximum norm on $\mathbb{R}^2$ are parallelograms
-- statement:
--   Equip $\mathbb{R}^2$ with the maximum norm $\|x\|_\infty=\max(|x_1|,|x_2|)$. A set $P\subseteq\mathbb{R}^2$ is a *parallelogram* if there are $c,u,w\in\mathbb{R}^2$ with $u,w$ linearly independent such that $P=\{c+su+tw:\ s,t\in[0,1]\}$.
--
--   For every centre $b\in\mathbb{R}^2$ and every radius $a>0$, the closed ball
--   $$
--   \bar B_\infty(b,a)=\{x\in\mathbb{R}^2:\ \|x-b\|_\infty\le a\}
--   $$
--   is a parallelogram. Geometrically, this ball is the axis-parallel square $[b_1-a,b_1+a]\times[b_2-a,b_2+a]$.
--
--   In the covering construction the lattice centres are surrounded by such sup-norm balls; their images under an invertible linear frame are again parallelograms and serve as cross-sections of parallelogram cylinders.
--
--   **Formalization Note** The ball lives in `Coordinates` (the type `Fin 2 → ℝ`), whose Mathlib norm is the sup norm, and `IsParallelogram` asks for `LinearIndependent ℝ ![u, v]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Frames.lean#L57-L87

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.coordinates_closedBall_parallelogram (b : Coordinates) {a : ℝ} (ha : 0 < a) :
    IsParallelogram (closedBall b a) := by sorry
