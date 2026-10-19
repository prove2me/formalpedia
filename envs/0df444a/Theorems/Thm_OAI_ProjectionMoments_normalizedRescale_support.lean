-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_normalizedRescale_support
-- name    : OAI.ProjectionMoments.normalizedRescale_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:46:48.625961+00:00
-- url     : https://prove2.me/theorems/6ed0eb3b-3887-469e-bef5-f89a488f0839
-- title:
--   Normalized rescaling moves the support into the unit ball
-- statement:
--   If $\nu$ is supported in the closed ball $\bar B(z,R)$ with $R>0$, then for all constants $K,a$ the normalized rescaling $(KR^a)^{-1}\,(x\mapsto R^{-1}(x-z))_*\nu$ is supported in the closed unit ball:
--   $$
--   \operatorname{supp}\subseteq\bar B(0,1).
--   $$
--
--   It reduces all estimates to measures supported in the unit ball.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Graph.lean#L317-L331

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

theorem OAI.ProjectionMoments.normalizedRescale_support {ν : Measure E} (K a : ℝ) (z : E) {R : ℝ}
    (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R) :
    (normalizedRescale ν K a z R).support ⊆ Metric.closedBall 0 1 := by sorry
