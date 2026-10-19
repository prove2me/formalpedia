-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_streaming_success_bound_tagged
-- name    : OAI.NoiselessRegression.Learner.streaming_success_bound_tagged
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:25:20.767313+00:00
-- url     : https://prove2.me/theorems/614baf40-2e07-4811-be2d-1059b66c39b1
-- title:
--   Success bound for memory-bounded streaming regression learners
-- statement:
--   A learner with $M$ bits of memory reads $T$ noiseless observations $(x_i,\langle s,x_i\rangle)$ of an unknown unit vector $s\in\mathbb R^d$, where the $x_i$ are independent standard Gaussians. Its rules may depend on a random seed $\omega\sim\rho$: an initial choice, transitions $\mathrm{State}\times(\mathbb R^d\times\mathbb R)\to\{\text{stop},\text{continue}\}\times\mathrm{State}$ with $|\mathrm{State}|=2^M$, and an output map to the unit sphere. Its uniform success probability at accuracy $\varepsilon$ is the probability, over a uniform $s$, the seed and the samples, that the output $\hat s$ has angular error $\arccos\langle\hat s,s\rangle\le\varepsilon$. Let the learner be admissible (its rules are measurable almost surely in the seed), $d\ge3$, $\varepsilon>0$, and let $a,q$ satisfy $2a\le d-1$, $q\ge2$ and $2q\le a$. With $J$ the tagged state set (states plus stopping times), $|J|=2^M(T+2)$, its uniform success probability satisfies
--   $$
--   \Pr\bigl[\arccos\langle\hat s,s\rangle\le\varepsilon\bigr]\le3\cdot4^d\,\varepsilon^a\cdot\Bigl(32768^d\,|J|^{1/q}\Bigr)^{\lceil T/q\rceil}.
--   $$
--
--   So a learner with little memory cannot locate $s$ to high accuracy unless it reads many samples.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Stopping.lean#L260-L288

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

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
variable {d M T : ℕ} {Ω : Type u}

theorem OAI.NoiselessRegression.Learner.streaming_success_bound_tagged [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := TaggedState M T) q ^ ((T+q-1)/q) := by sorry
