-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_capTest_allBall
-- name    : OAI.ProjectionMoments.capTest_allBall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:12:58.663423+00:00
-- url     : https://prove2.me/theorems/bdbbe042-f102-47ee-88b6-4465ded35c2c
-- title:
--   Cap test measures satisfy a uniform ball-mass bound
-- statement:
--   Let $\sigma$ be the normalized surface measure on the unit sphere of $E$ (of dimension $n$). For a centre $c$ and a radius $r>0$, the cap measure $\sigma_{c,r}$ is $\sigma$ restricted to $\bar B(c,r)$ and normalized to total mass one. Assume $E$ is nontrivial, $\|c\|=1$, $0<r\le2$, $\alpha\ge0$ with $2\alpha=n-1$, and let $(c_i,\rho_i)$ be a cap dictionary for $(c,r,\alpha)$. Let $h\ge0$ satisfy the dual condition $\int h\,d\sigma_{c_i,\rho_i}\le(r/\rho_i)^\alpha$ for every $i$. Then the cap test measure $\mu$, the image of $h\,\sigma_{c,r}$ under $x\mapsto r^{-1}(x-c)$, satisfies for all $b$ and $t>0$
--   $$
--   \mu\bigl(\bar B(b,t)\bigr)\le2048^n\,t^\alpha .
--   $$
--
--   Thus the dual cap condition gives the ball-mass hypothesis for the rescaled measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/CapTests.lean#L127-L181

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

theorem OAI.ProjectionMoments.capTest_allBall [Nontrivial E] {h : E → ℝ≥0∞} {c : E} (hc : ‖c‖ = 1)
    {r α : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hα0 : 0 ≤ α)
    (hα : 2*α = (Module.finrank ℝ E-1:ℕ)) (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    AllBallMass (capTestMeasure h c r) ((2048:ℝ)^Module.finrank ℝ E) α := by sorry
