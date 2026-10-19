-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_gaussian_norm_ball_mass
-- name    : OAI.ProjectionMoments.gaussian_norm_ball_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:49:13.117786+00:00
-- url     : https://prove2.me/theorems/74466360-c3ab-40e5-8457-1c8c605960b8
-- title:
--   A standard Gaussian vector has norm at most √(2n) with probability at least ½
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on a real inner product space of dimension $n>0$. Then
--   $$
--   \gamma\bigl(\bar B(0,\sqrt{2n})\bigr)\ge\tfrac12 .
--   $$
--
--   It shows that Gaussian rows are typically of size about $\sqrt n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/GaussianDensity.lean#L102-L130

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

theorem OAI.ProjectionMoments.gaussian_norm_ball_mass (hd : 0 < Module.finrank ℝ E) :
    (2 : ℝ≥0∞)⁻¹ ≤ stdGaussian E (Metric.closedBall 0 (Real.sqrt (2 * Module.finrank ℝ E))) := by sorry
