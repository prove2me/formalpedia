-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_exists_equivalent_tape
-- name    : OAI.NoiselessRegression.FiniteKernelLearner.exists_equivalent_tape
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:49:17.26998+00:00
-- url     : https://prove2.me/theorems/cbb94c49-c5fd-4e35-a7fb-a0fd4361bdd3
-- title:
--   Finite kernel learners are equivalent to seeded deterministic learners
-- statement:
--   A finite kernel learner with $M$ bits of memory and horizon $T$ on $\mathbb R^d$ consists of an initial law on $\{\text{stop},\text{continue}\}\times\mathrm{State}$, transition kernels $K_t(j,\mathrm{obs})$ on the same set, and output laws on the unit sphere, where $|\mathrm{State}|=2^M$. It reads noiseless observations $(x_i,\langle s,x_i\rangle)$ with Gaussian $x_i$. It has completed rules if each transition probability $\mathrm{obs}\mapsto K_t(j,\mathrm{obs})\{a\}$ is measurable with respect to the completion of the observation reference law (Gaussian times Lebesgue). Its uniform success at accuracy $\varepsilon$ is the probability that the output has angular error at most $\varepsilon$, for uniform $s$ and Gaussian samples; the fixed-time success additionally requires the stop to happen at time $t$. If $K$ has completed rules and $d\ge3$, then there are a probability measure $\rho$ on tapes (initial choice, transition coins, output coin) and a deterministic learner $L$ driven by the tape, with measurable rules and admissible for $\rho$, such that for all $\varepsilon$ and $t$
--   $$
--   \mathrm{succ}_\rho(L,\varepsilon)=\mathrm{succ}(K,\varepsilon),\qquad\mathrm{succ}_\rho(L,\varepsilon,t)=\mathrm{succ}(K,\varepsilon,t).
--   $$
--
--   Randomized finite-state learners therefore add no power beyond seeded deterministic ones.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Seeded.lean#L92-L111

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
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
import Definitions.Def_OAI_Probability_ProjectionMoments_Seeded

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open Learner
variable {d M T : ℕ}

theorem OAI.NoiselessRegression.FiniteKernelLearner.exists_equivalent_tape (K : FiniteKernelLearner d M T) (hK : K.CompletedRules) (hd : 3 ≤ d) :
    ∃ (ρ : Measure (Tape M T)) (L : Learner d M T (Tape M T)),
      IsProbabilityMeasure ρ ∧ L.MeasurableRules ∧ L.Admissible ρ ∧
      (∀ ε, L.uniformSuccess ρ ε = K.uniformSuccess ε) ∧
      (∀ ε t, L.uniformFixedSuccess ρ ε t = K.uniformFixedSuccess ε t) := by sorry
