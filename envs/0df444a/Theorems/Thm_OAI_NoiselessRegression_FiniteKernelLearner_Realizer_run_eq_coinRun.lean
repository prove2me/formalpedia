-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_Realizer_run_eq_coinRun
-- name    : OAI.NoiselessRegression.FiniteKernelLearner.Realizer.run_eq_coinRun
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:33:34.818007+00:00
-- url     : https://prove2.me/theorems/74af37b9-a77c-4661-8e03-fa741a9a6a4e
-- title:
--   The realized learner run is a coin run on tagged states
-- statement:
--   A finite kernel learner with $M$ bits of memory and horizon $T$ consists of an initial law on $\{\text{stop},\text{continue}\}\times\mathrm{State}$, transition kernels $K_t(j,\mathrm{obs})$ on the same set, and output laws $K^{\mathrm{out}}_t(j)$ on the unit sphere of $\mathbb R^d$, where $|\mathrm{State}|=2^M$. A realizer represents these kernels by measurable maps of a uniform coin $u\in[0,1]$, so that the law of $\phi_t(j,\mathrm{obs},u)$ is $K_t(j,\mathrm{obs})$ and the law of $g_t(j,u)$ is $K^{\mathrm{out}}_t(j)$. Let $L_R$ be the deterministic learner built from a realizer $R$ and driven by the tape $\omega=(\text{initial choice},(u_1,\dots,u_T),u_{\mathrm{out}})$. For $s$ on the unit sphere, samples $x$ and $n\le T$, the run status of $L_R$ after $n$ steps equals
--   $$
--   \mathrm{run}_n(L_R;s,\omega,x)=\mathrm{decode}\Bigl(R_n\bigl(\mathrm{start}(\omega_0),(x_i,\langle s,x_i\rangle)_{i<n},(u_i)_{i<n}\bigr)\Bigr),
--   $$
--   where $R_n$ is the coin run of the tagged transition (stopped states are absorbing and carry their stopping time) and $\mathrm{decode}$ turns tagged states into run statuses.
--
--   The realized learner is literally a coin-driven run on the tagged state space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Realization.lean#L114-L135

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

theorem OAI.NoiselessRegression.FiniteKernelLearner.Realizer.run_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) {n : ℕ} (hn : n ≤ T) :
    R.toLearner.run s ω x n = decodeTagged
      (coinRun R.taggedTransition n (taggedStart ω.1)
        (fun i => (x (Fin.castLE hn i),⟪s.val,x (Fin.castLE hn i)⟫))
        (fun i => ω.2.1 (Fin.castLE hn i))) := by sorry
