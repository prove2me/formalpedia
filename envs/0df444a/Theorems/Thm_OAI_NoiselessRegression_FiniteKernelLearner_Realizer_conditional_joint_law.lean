-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_Realizer_conditional_joint_law
-- name    : OAI.NoiselessRegression.FiniteKernelLearner.Realizer.conditional_joint_law
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:34:18.373084+00:00
-- url     : https://prove2.me/theorems/d122c098-640a-4492-8a12-a826f3c68a25
-- title:
--   The realized learner has the joint law of the kernel experiment
-- statement:
--   A finite kernel learner with $M$ bits of memory and horizon $T$ consists of an initial law on $\{\text{stop},\text{continue}\}\times\mathrm{State}$, transition kernels $K_t(j,\mathrm{obs})$ on the same set, and output laws $K^{\mathrm{out}}_t(j)$ on the unit sphere of $\mathbb R^d$, where $|\mathrm{State}|=2^M$. A realizer represents these kernels by measurable maps of a uniform coin $u\in[0,1]$, so that the law of $\phi_t(j,\mathrm{obs},u)$ is $K_t(j,\mathrm{obs})$ and the law of $g_t(j,u)$ is $K^{\mathrm{out}}_t(j)$. Let $L_R$ be the deterministic learner built from a realizer $R$. For each unit vector $s$ and samples $x$, the joint law of its terminal (time, state) pair and its estimate, under the tape law (initial choice from the initial law, independent uniform coins), equals the joint experiment law of $K$:
--   $$
--   \mathrm{Law}_\omega\bigl(\mathrm{terminal}(s,\omega,x),\ \mathrm{estimate}(s,\omega,x)\bigr)=\mathrm{JointLaw}_K\bigl((x_i,\langle s,x_i\rangle)_i\bigr).
--   $$
--
--   So the coin realization reproduces the randomized learner exactly, conditionally on the samples.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Realization.lean#L212-L241

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

theorem OAI.NoiselessRegression.FiniteKernelLearner.Realizer.conditional_joint_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (x : Samples d T) :
    K.tapeLaw.map (fun ω => (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) =
      K.jointExperimentLaw (fun i => (x i,⟪s.val,x i⟫)) := by sorry
