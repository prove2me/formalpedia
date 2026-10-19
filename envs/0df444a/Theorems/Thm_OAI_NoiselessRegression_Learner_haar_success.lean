-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_haar_success
-- name    : OAI.NoiselessRegression.Learner.haar_success
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:47:36.511229+00:00
-- url     : https://prove2.me/theorems/86f4e8c2-40a2-41fe-a66a-c466d3c32a9a
-- title:
--   Success bound for streaming regression with optimal accuracy exponent
-- statement:
--   A learner with $M$ bits of memory reads $T$ noiseless observations $(x_i,\langle s,x_i\rangle)$ of an unknown unit vector $s\in\mathbb R^d$, where the $x_i$ are independent standard Gaussians. Its rules may depend on a random seed $\omega\sim\rho$: an initial choice, transitions $\mathrm{State}\times(\mathbb R^d\times\mathbb R)\to\{\text{stop},\text{continue}\}\times\mathrm{State}$ with $|\mathrm{State}|=2^M$, and an output map to the unit sphere. It is admissible if its rules are measurable almost surely in the seed. Its uniform success probability at accuracy $\varepsilon$ is the probability, over a uniform $s$, the seed and the samples, that the output $\hat s$ satisfies $\arccos\langle\hat s,s\rangle\le\varepsilon$. There is $C\ge1$ such that for all $d\ge16$, $M$, $T$, $0<\varepsilon\le1/10$ and every admissible learner, with $k=\lfloor d/4\rfloor$ and $N_*=(k+2)2^M$,
--   $$
--   \Pr\bigl[\arccos\langle\hat s,s\rangle\le\varepsilon\bigr]\le C^d\,\varepsilon^k\,\Bigl(C^dN_*^{1/k}\Bigr)^{\lceil T/k\rceil}.
--   $$
--
--   Unlike the tagged bound, the per-block factor does not grow with $T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Streaming.lean#L365-L393

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

theorem OAI.NoiselessRegression.Learner.haar_success :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      L.uniformSuccess ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k)) := by sorry
