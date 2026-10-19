-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_rescaled_projection_ac
-- name    : OAI.ProjectionMoments.rescaled_projection_ac
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:14:06.40098+00:00
-- url     : https://prove2.me/theorems/1608876c-917b-48fa-806f-71e3ddd9b8e9
-- title:
--   Absolute continuity of projections is preserved by rescaling
-- statement:
--   Let $\nu$ be a measure on a finite-dimensional real inner product space $E$, let $A=(A_1,\dots,A_k)$ be vectors in $E$, and let $P_A(x)=(\langle x,A_i\rangle)_i\in\mathbb R^k$. Let $c\in E$ and $r>0$, and let $\phi(x)=r^{-1}(x-c)$. If $(P_A)_*\nu\ll\mathrm{vol}_k$, then
--   $$
--   (P_A)_*(\phi_*\nu)\ll\mathrm{vol}_k .
--   $$
--
--   Rescaling the measure does not destroy absolute continuity of its coordinate projections.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/CapTests.lean#L183-L201

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
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.rescaled_projection_ac {ν : Measure E} {k : ℕ} (A : Fin k → E) (c : E) {r : ℝ} (hr : 0 < r)
    (hν : ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (ν.map (rescale c r)).map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by sorry
