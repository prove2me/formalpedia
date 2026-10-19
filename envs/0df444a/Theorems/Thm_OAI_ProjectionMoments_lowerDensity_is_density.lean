-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_lowerDensity_is_density
-- name    : OAI.ProjectionMoments.lowerDensity_is_density
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:44:13.465116+00:00
-- url     : https://prove2.me/theorems/ab28d894-cac8-4105-be5a-3adcdf92ccf2
-- title:
--   The lower density is a density of the projected measure
-- statement:
--   For a measure $\nu$ on a finite-dimensional inner product space $E$ and rows $A=(A_1,\dots,A_m)$, the row map is $x\mapsto(\langle x,A_j\rangle)_j\in\mathbb R^m$; the ball average at $(A,y)$ with radius $\eta$ is the $\nu$-mass whose projection lies in $\bar B(y,\eta)$ divided by the volume of that ball, and the lower density is the $\liminf$ of ball averages along $\eta=1/(n+1)$. If $\nu$ is finite and its projection under the rows $A$ is absolutely continuous with respect to Lebesgue measure, then the lower density represents it:
--   $$
--   \int_S\underline f_\nu(A,y)\,dy=\nu\bigl(\{x:\ (\langle x,A_j\rangle)_j\in S\}\bigr)\quad\text{for all measurable }S .
--   $$
--
--   Hence moment bounds for the lower density are moment bounds for the actual projected density.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Graph.lean#L205-L224

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

theorem OAI.ProjectionMoments.lowerDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (rowMap A) ≪ (volume : Measure (Label m))) :
    volume.withDensity (fun y => lowerDensity ν m (A,y)) = ν.map (rowMap A) := by sorry
