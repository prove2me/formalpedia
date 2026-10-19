-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_rieszPotential_ball_control
-- name    : OAI.ProjectionMoments.rieszPotential_ball_control
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:00:10.852989+00:00
-- url     : https://prove2.me/theorems/723746ff-45e7-4797-9114-4383bb2330a7
-- title:
--   Riesz potentials control ball masses
-- statement:
--   For a density $0\le h\le1$ on the unit sphere of $E$, the Riesz potential with exponent $\alpha$ is $\sup_z\int h(s)\,\|s-z\|^{-\alpha}\,d\sigma(s)$, where $\sigma$ is the normalized surface measure. For measurable $h$, every centre $z$ and radius $r>0$,
--   $$
--   \int_{\bar B(z,r)}h\,d\sigma\le\Bigl(\sup_{z'}\int h(s)\|s-z'\|^{-\alpha}d\sigma(s)\Bigr)\,r^{\alpha} .
--   $$
--
--   So a finite Riesz potential gives a mass bound with exponent $\alpha$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/RieszPotential.lean#L116-L142

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

theorem OAI.ProjectionMoments.rieszPotential_ball_control [Nontrivial E] {α : ℝ} (hα : 0 ≤ α)
    {h : E → ℝ≥0∞} (hh : Measurable h) (z : E) {r : ℝ} (hr : 0 < r) :
    (NoiselessRegression.ambientSphereLaw.withDensity h) (Metric.closedBall z r) ≤
      rieszPotential α h * ENNReal.ofReal (r^α) := by sorry
