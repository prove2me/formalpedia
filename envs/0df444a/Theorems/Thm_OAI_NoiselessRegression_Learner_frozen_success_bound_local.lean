-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_frozen_success_bound_local
-- name    : OAI.NoiselessRegression.Learner.frozen_success_bound_local
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:46:30.357992+00:00
-- url     : https://prove2.me/theorems/27e8c63d-dd90-43f4-a402-548d22f6833f
-- title:
--   Success bound for a learner with frozen seed using local tags
-- statement:
--   A learner with $M$ bits of memory reads $T$ noiseless observations $(x_i,\langle s,x_i\rangle)$ of an unknown unit vector $s\in\mathbb R^d$, where the $x_i$ are independent standard Gaussians. Its rules may depend on a random seed $\omega\sim\rho$: an initial choice, transitions $\mathrm{State}\times(\mathbb R^d\times\mathbb R)\to\{\text{stop},\text{continue}\}\times\mathrm{State}$ with $|\mathrm{State}|=2^M$, and an output map to the unit sphere. It is admissible if its rules are measurable almost surely in the seed. Its uniform success probability at accuracy $\varepsilon$ is the probability, over a uniform $s$, the seed and the samples, that the output $\hat s$ satisfies $\arccos\langle\hat s,s\rangle\le\varepsilon$. Here $\Phi_q=32768^{\,d}\,\bigl(2^M(q+2)\bigr)^{1/q}$ is the stream factor of the locally tagged state set (states together with a stopping position inside a block of length $q$). Fix a seed $\omega$ for which all transitions are measurable, and let $d\ge3$, $0<\varepsilon\le1$, $b\ge0$, $a+b\le d-1$, $q\ge2$ and $2q\le a$. Then, over a uniform $s$ and Gaussian samples,
--   $$
--   \Pr\bigl[\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr]\le3\cdot4^d\,\varepsilon^b\,\Phi_q^{\lceil T/q\rceil}.
--   $$
--
--   Only the position of a stop within the current block has to be remembered, not the global stopping time.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Streaming.lean#L284-L333

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

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
variable {d M T : ℕ} {Ω : Type u}

theorem OAI.NoiselessRegression.Learner.frozen_success_bound_local (L : Learner d M T Ω) (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (L.transition t ω j) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ)) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by sorry
