-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_ballAverage_eq
-- name    : OAI.ProjectionMoments.ballAverage_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:43:34.082779+00:00
-- url     : https://prove2.me/theorems/7c0caea3-9fd7-4892-acd4-125d896c97ef
-- title:
--   Ball averages are normalized projected masses
-- statement:
--   For a measure $\nu$ on a finite-dimensional inner product space $E$ and rows $A=(A_1,\dots,A_m)$, the row map is $x\mapsto(\langle x,A_j\rangle)_j\in\mathbb R^m$; the ball average at $(A,y)$ with radius $\eta$ is the $\nu$-mass whose projection lies in $\bar B(y,\eta)$ divided by the volume of that ball, and the lower density is the $\liminf$ of ball averages along $\eta=1/(n+1)$. For s-finite $\nu$, rows $A$, a label $y$ and a radius $\eta$,
--   $$
--   \mathrm{avg}_\eta(A,y)=\frac{\nu\bigl(\{x:\ (\langle x,A_j\rangle)_j\in\bar B(y,\eta)\}\bigr)}{\mathrm{vol}\bigl(\bar B(y,\eta)\bigr)} .
--   $$
--
--   Their $\liminf$ defines the lower density.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Graph.lean#L143-L168

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem OAI.ProjectionMoments.ballAverage_eq (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage ν m η (A,y) =
      (ν.map (rowMap A)) (Metric.closedBall y η) /
        volume (Metric.closedBall y η) := by sorry
