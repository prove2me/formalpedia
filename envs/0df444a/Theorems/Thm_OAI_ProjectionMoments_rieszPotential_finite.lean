-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_rieszPotential_finite
-- name    : OAI.ProjectionMoments.rieszPotential_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:59:11.748696+00:00
-- url     : https://prove2.me/theorems/8daad1b4-3e71-457c-8e7c-bcfd22e1ddd0
-- title:
--   Riesz potentials of bounded sphere densities are finite
-- statement:
--   For a density $0\le h\le1$ on the unit sphere of $E$, the Riesz potential with exponent $\alpha$ is $\sup_z\int h(s)\,\|s-z\|^{-\alpha}\,d\sigma(s)$, where $\sigma$ is the normalized surface measure. If $0\le\alpha\le m$ and $m+1\le\dim E-1$, then
--   $$
--   \sup_z\int h(s)\,\|s-z\|^{-\alpha}\,d\sigma(s)<\infty .
--   $$
--
--   So the Riesz potential is a meaningful size measure for such densities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/RieszPotential.lean#L87-L114

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

theorem OAI.ProjectionMoments.rieszPotential_finite [Nontrivial E] {α : ℝ} (hα : 0 ≤ α) {m : ℕ}
    (hm : α ≤ m) (hmd : m+1 ≤ Module.finrank ℝ E-1)
    {h : E → ℝ≥0∞} (h1 : ∀ s, h s ≤ 1) : rieszPotential α h < ∞ := by sorry
