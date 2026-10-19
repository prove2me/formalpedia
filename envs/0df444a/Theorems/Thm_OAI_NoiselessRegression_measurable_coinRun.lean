-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_measurable_coinRun
-- name    : OAI.NoiselessRegression.measurable_coinRun
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:30:47.034173+00:00
-- url     : https://prove2.me/theorems/6d4ec7ff-fff1-432d-87ba-f673872e362f
-- title:
--   Measurability of coin-driven finite-state runs
-- statement:
--   Let $J$ be a finite state set and let $F_t(j,o,\cdot):[0,1]\to J$ be measurable for every time $t$, state $j$ and observation $o$. For fixed $n$, start state $j$ and observations $o_1,\dots,o_n$, the coin run $R_n(j,o,u)$ is defined by $R_0=j$ and $R_{t+1}=F_{t+1}(R_t,o_{t+1},u_{t+1})$. Then the map
--   $$
--   u=(u_1,\dots,u_n)\in[0,1]^n\longmapsto R_n(j,o,u)\in J
--   $$
--   is measurable.
--
--   The final state of a coin-driven run thus depends measurably on the coins.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Kernels.lean#L70-L84

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

omit [MeasurableSpace O] in
theorem OAI.NoiselessRegression.measurable_coinRun [MeasurableSpace O] {F : ℕ → J → O → I → J}
    (hF : ∀ t j obs, Measurable (F t j obs)) (n : ℕ) (j : J) (obs : Fin n → O) :
    Measurable (coinRun F n j obs) := by sorry
