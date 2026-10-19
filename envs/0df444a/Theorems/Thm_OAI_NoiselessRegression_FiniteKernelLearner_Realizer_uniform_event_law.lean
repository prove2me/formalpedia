-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_Realizer_uniform_event_law
-- name    : OAI.NoiselessRegression.FiniteKernelLearner.Realizer.uniform_event_law
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:48:27.466977+00:00
-- url     : https://prove2.me/theorems/52a104cc-7f50-403a-a905-3d1c24ee9f28
-- title:
--   Event probabilities of the realized learner match the kernel experiment
-- statement:
--   Let $K$ be a finite kernel learner on $\mathbb R^d$ (initial law, transition kernels and output laws on $2^M$ states and horizon $T$), and let $R$ be a realizer of $K$ by uniform coins with associated deterministic learner $L_R$ driven by a tape $\omega$. For every measurable set $S$ of triples $(s,(\text{terminal},\text{estimate}))$,
--   $$
--   \Pr_{s,\omega,x}\Bigl[\bigl(s,(\mathrm{term}_{L_R}(s,\omega,x),\hat s_{L_R}(s,\omega,x))\bigr)\in S\Bigr]=\int\mathrm{JointLaw}_K\bigl((x_i,\langle s,x_i\rangle)_i\bigr)\{r:(s,r)\in S\}\,d(\sigma\otimes\gamma^{\otimes T})(s,x),
--   $$
--   where $s$ is uniform on the sphere, $\omega$ follows the tape law and $x$ the Gaussian sample law.
--
--   So any success event can be computed in the kernel model.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Seeded.lean#L17-L40

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

theorem OAI.NoiselessRegression.FiniteKernelLearner.Realizer.uniform_event_law [NeZero d] {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (S : Set (UnitSphere d × Result d M)) (hS : MeasurableSet S) :
    ((uniformSphere d).prod (K.tapeLaw.prod (sampleLaw d T)))
      {z | (z.1,(R.toLearner.terminal z.1 z.2.1 z.2.2,R.toLearner.estimate z.1 z.2.1 z.2.2)) ∈ S} =
    ∫⁻ z : UnitSphere d × Samples d T,
      K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫))
        {r | (z.1,r) ∈ S} ∂((uniformSphere d).prod (sampleLaw d T)) := by sorry
