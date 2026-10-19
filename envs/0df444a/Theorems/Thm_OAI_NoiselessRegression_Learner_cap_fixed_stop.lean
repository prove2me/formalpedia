-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_cap_fixed_stop
-- name    : OAI.NoiselessRegression.Learner.cap_fixed_stop
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:45:46.282068+00:00
-- url     : https://prove2.me/theorems/df893138-3492-40d4-b2d4-3957f298a28a
-- title:
--   Success bound at a fixed stopping time
-- statement:
--   A learner with $M$ bits of memory reads $T$ noiseless observations $(x_i,\langle s,x_i\rangle)$ of an unknown unit vector $s\in\mathbb R^d$, where the $x_i$ are independent standard Gaussians. Its rules may depend on a random seed $\omega\sim\rho$: an initial choice, transitions $\mathrm{State}\times(\mathbb R^d\times\mathbb R)\to\{\text{stop},\text{continue}\}\times\mathrm{State}$ with $|\mathrm{State}|=2^M$, and an output map to the unit sphere. It is admissible if its rules are measurable almost surely in the seed. Its uniform success probability at accuracy $\varepsilon$ is the probability, over a uniform $s$, the seed and the samples, that the output $\hat s$ satisfies $\arccos\langle\hat s,s\rangle\le\varepsilon$. There is $C>0$ such that the following holds for $d\ge32$, $0<\varepsilon\le1/10$, $k=\lfloor d/16\rfloor$ and $\alpha=(d-1)/2$. Let the learner be admissible, with an almost surely measurable stopping time, and let $t\le T$. Then the probability that the learner stops at time $t$ with angular error at most $\varepsilon$ satisfies
--   $$
--   \Pr\bigl[\text{stop at }t,\ \arccos\langle\hat s,s\rangle\le\varepsilon\bigr]\le e^{Cd}\Bigl(\frac\varepsilon2\Bigr)^\alpha\Bigl(e^{Cd}\,2^{M/k}\Bigr)^{\lceil t/k\rceil}.
--   $$
--
--   At a fixed time no stopping tags are needed, so the per-block cost involves only $2^M$ states.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Streaming.lean#L218-L277

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

theorem OAI.NoiselessRegression.Learner.cap_fixed_stop :
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      AEMeasurable (fun z : UnitSphere d × (Ω × Samples d T) =>
        (L.terminal z.1 z.2.1 z.2.2).1) ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      L.uniformFixedSuccess ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((t+k-1)/k)) := by sorry
