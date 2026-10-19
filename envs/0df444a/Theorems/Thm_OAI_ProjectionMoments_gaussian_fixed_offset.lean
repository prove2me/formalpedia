-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_gaussian_fixed_offset
-- name    : OAI.ProjectionMoments.gaussian_fixed_offset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:58:31.933056+00:00
-- url     : https://prove2.me/theorems/321a863f-12ee-4929-9d5b-18f2326a7cf3
-- title:
--   Gaussian L^q bound of lower densities at a fixed offset
-- statement:
--   Let $\nu$ be finite with all-ball mass bound $(K,a)$, $K\ge0$, supported in $\bar B(z,R)$, and let $q\ge1$, $q+m\le a\le n=\dim E$. Then for every offset $b\in\mathbb R^m$,
--   $$
--   \Bigl(\int\underline f_\nu\bigl(A,(\langle z,A_j\rangle)_j+b\bigr)^q\,d\gamma^{\otimes m}(A)\Bigr)^{1/q}\le128^{n}\,K\,R^{a-m} .
--   $$
--
--   It is the fixed-offset form of the replica moment bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/RieszPotential.lean#L13-L47

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.gaussian_fixed_offset {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 ≤ K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hq : 1 ≤ q) (hmargin : (q:ℝ)+m ≤ a)
    (ha : a ≤ Module.finrank ℝ E) (b : Label m) :
    (∫⁻ A : Fin m → E, (lowerDensity ν m (A,rowMap A z+b))^q
      ∂Measure.pi (fun _ => stdGaussian E))^(1/(q:ℝ)) ≤
      ENNReal.ofReal ((128:ℝ)^Module.finrank ℝ E * K * R^(a-m)) := by sorry
