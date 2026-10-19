-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_exists_realizer
-- name    : OAI.NoiselessRegression.FiniteKernelLearner.exists_realizer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:32:58.562502+00:00
-- url     : https://prove2.me/theorems/3abc8c35-79ef-41c6-a15c-8ded34728616
-- title:
--   Finite kernel learners with Borel rules admit coin realizers
-- statement:
--   A finite kernel learner with $M$ bits of memory and horizon $T$ consists of an initial law on $\{\text{stop},\text{continue}\}\times\mathrm{State}$, transition kernels $K_t(j,\mathrm{obs})$ on the same set, and output laws $K^{\mathrm{out}}_t(j)$ on the unit sphere of $\mathbb R^d$, where $|\mathrm{State}|=2^M$. A realizer represents these kernels by measurable maps of a uniform coin $u\in[0,1]$, so that the law of $\phi_t(j,\mathrm{obs},u)$ is $K_t(j,\mathrm{obs})$ and the law of $g_t(j,u)$ is $K^{\mathrm{out}}_t(j)$. If every transition kernel $\mathrm{obs}\mapsto K_t(j,\mathrm{obs})$ is measurable (Borel rules), then $K$ admits a realizer: there are maps $\phi_t$ and $g_t$ with $(j,\mathrm{obs},u)\mapsto\phi_t(j,\mathrm{obs},u)$ jointly measurable in $(\mathrm{obs},u)$, $g_t(j,\cdot)$ measurable, and
--   $$
--   \mathrm{Law}_u\,\phi_t(j,\mathrm{obs},u)=K_t(j,\mathrm{obs}),\qquad\mathrm{Law}_u\,g_t(j,u)=K^{\mathrm{out}}_t(j).
--   $$
--
--   So randomized kernels can be simulated by deterministic rules fed with uniform coins.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Realization.lean#L22-L37

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
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
open Learner
variable {d M T : ℕ}

theorem OAI.NoiselessRegression.FiniteKernelLearner.exists_realizer (K : FiniteKernelLearner d M T) (hK : K.BorelRules) : Nonempty K.Realizer := by sorry
