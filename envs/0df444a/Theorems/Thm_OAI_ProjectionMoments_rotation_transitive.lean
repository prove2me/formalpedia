-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_rotation_transitive
-- name    : OAI.ProjectionMoments.rotation_transitive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:51:04.698459+00:00
-- url     : https://prove2.me/theorems/6ce89fe3-aa04-41c5-950c-48f09d698388
-- title:
--   Rotations act transitively on orthonormal frames
-- statement:
--   For two orthonormal families $u,v$ indexed by the same finite set in a finite-dimensional inner product space $E$, there is a linear isometry (rotation) $O$ of $E$ with
--   $$
--   O(u_i)=v_i\quad\text{for all }i .
--   $$
--
--   Hence the rotation-invariant frame law does not depend on the starting frame.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Frames.lean#L40-L64

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {E}

theorem OAI.ProjectionMoments.rotation_transitive {ι : Type*} [Fintype ι] {u v : ι → E}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    ∃ O : Rotation E, ∀ i, (O : E →L[ℝ] E) (u i) = v i := by sorry
