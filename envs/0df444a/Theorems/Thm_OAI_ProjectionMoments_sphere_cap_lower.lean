-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_sphere_cap_lower
-- name    : OAI.ProjectionMoments.sphere_cap_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:08:59.714368+00:00
-- url     : https://prove2.me/theorems/b207613c-a737-4d3d-8d1a-b54ea320d580
-- title:
--   Lower bound for the surface measure of spherical caps
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner product space of dimension $n$, and let $\sigma$ be the normalized surface measure on its unit sphere. For every unit vector $c$ and every $0<r\le2$,
--   $$
--   r^{\,n-1}\le16^n\,\sigma\bigl(\bar B(c,r)\bigr).
--   $$
--
--   So a cap of radius $r$ carries surface measure at least $16^{-n}r^{n-1}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Caps.lean#L184-L209

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.sphere_cap_lower [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ENNReal.ofReal (r^(Module.finrank ℝ E-1)) ≤
      ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) *
        NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) := by sorry
