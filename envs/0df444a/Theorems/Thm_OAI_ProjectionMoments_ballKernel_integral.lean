-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_ballKernel_integral
-- name    : OAI.ProjectionMoments.ballKernel_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:41:02.294731+00:00
-- url     : https://prove2.me/theorems/245ebadf-d8d6-4560-9ae7-bfc43fd2752a
-- title:
--   The normalized ball kernel has integral one
-- statement:
--   For $\eta>0$, the ball kernel on $\mathbb R^m$, equal to $1/\mathrm{vol}(\bar B(0,\eta))$ on the closed ball of radius $\eta$ and $0$ outside, is a probability density:
--   $$
--   \int_{\mathbb R^m}\frac{\mathbf 1_{\bar B(0,\eta)}(y)}{\mathrm{vol}(\bar B(0,\eta))}\,dy=1 .
--   $$
--
--   So ball averages are smoothings by a probability kernel.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Graph.lean#L111-L124

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

theorem OAI.ProjectionMoments.ballKernel_integral (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ y, ballKernel m η y = 1 := by sorry
