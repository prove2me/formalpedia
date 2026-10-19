-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_riesz_success
-- name    : OAI.NoiselessRegression.Learner.riesz_success
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:44:58.604178+00:00
-- url     : https://prove2.me/theorems/25a32103-7f6b-416e-83cb-719e1e3a1a30
-- title:
--   Exponential success bound for streaming regression with logarithmic slack
-- statement:
--   A learner with $M$ bits of memory reads $T$ noiseless observations $(x_i,\langle s,x_i\rangle)$ of an unknown unit vector $s\in\mathbb R^d$, where the $x_i$ are independent standard Gaussians. Its rules may depend on a random seed $\omega\sim\rho$: an initial choice, transitions $\mathrm{State}\times(\mathbb R^d\times\mathbb R)\to\{\text{stop},\text{continue}\}\times\mathrm{State}$ with $|\mathrm{State}|=2^M$, and an output map to the unit sphere. It is admissible if its rules are measurable almost surely in the seed. Its uniform success probability at accuracy $\varepsilon$ is the probability, over a uniform $s$, the seed and the samples, that the output $\hat s$ satisfies $\arccos\langle\hat s,s\rangle\le\varepsilon$. There is $C_0\ge1$ such that for all $d\ge16$, $M$, $T$, $0<\varepsilon\le1/10$ and every admissible learner, with $q=\lfloor d/8\rfloor$ and $W=(T+2)2^M$,
--   $$
--   \Pr\bigl[\arccos\langle\hat s,s\rangle\le\varepsilon\bigr]\le C_0^d\,\varepsilon^{d/2-1}\Bigl(1+C_0^d\bigl(1+\log\tfrac1\varepsilon\bigr)W^{1/q}\Bigr)^{\lceil T/q\rceil}.
--   $$
--
--   The factor $\varepsilon^{d/2-1}$ shows that each block of $q$ samples gains at most a bounded factor per memory bit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Streaming.lean#L15-L77

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

theorem OAI.NoiselessRegression.Learner.riesz_success :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      L.uniformSuccess ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q)) := by sorry
