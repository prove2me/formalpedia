-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_sphere_frame_ac
-- name    : OAI.ProjectionMoments.sphere_frame_ac
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:55:33.602093+00:00
-- url     : https://prove2.me/theorems/3997a77f-839a-4510-9d83-55fb5d2c3e61
-- title:
--   Frame projections of the sphere measure are absolutely continuous
-- statement:
--   Let $E$ have dimension at least $m+2$ and let $u$ be an orthonormal $m$-frame. Then the image of the normalized surface measure of the unit sphere under $x\mapsto(\langle x,u_i\rangle)_i$ is absolutely continuous with respect to Lebesgue measure on $\mathbb R^m$:
--   $$
--   (\langle\cdot,u_i\rangle)_*\sigma\ll\mathrm{vol}_m .
--   $$
--
--   This supplies the absolute continuity hypothesis needed when the moment bounds are transferred from Gaussian rows to sphere-valued frames.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/SphereDensity.lean#L98-L115

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.sphere_frame_ac [Nontrivial E] {m : ℕ} (hm : m+2 ≤ Module.finrank ℝ E)
    {u : Fin m → E} (hu : Orthonormal ℝ u) :
    NoiselessRegression.ambientSphereLaw.map (coordinateMap u) ≪ (volume : Measure (Fin m → ℝ)) := by sorry
