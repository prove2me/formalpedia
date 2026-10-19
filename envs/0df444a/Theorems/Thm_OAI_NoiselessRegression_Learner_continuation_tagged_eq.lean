-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_continuation_tagged_eq
-- name    : OAI.NoiselessRegression.Learner.continuation_tagged_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:40:42.904982+00:00
-- url     : https://prove2.me/theorems/71239689-64ae-47e9-8e65-3b33151865ef
-- title:
--   Tagged continuations reduce to stopped continuations
-- statement:
--   Let $\tau_t:\mathrm{State}\times(\mathbb R^d\times\mathbb R)\to\{\text{stop},\text{continue}\}\times\mathrm{State}$ be stopping transitions on $2^M$ states and $w_t(j,\cdot)\in[0,1]$ weights on $\mathbb R^d$. The stopped continuation is defined by $V_{n,0}(j,s)=w_n(j,s)$ and $V_{n,k+1}(j,s)=\int\bigl[\text{if }\tau_{n+1}(j,(x,\langle s,x\rangle))=(\text{stop},a)\text{ then }w_{n+1}(a,s)\text{ else }V_{n+1,k}(a,s)\bigr]\,d\gamma(x)$. It is the expected weight at the stopping time, or at time $n+k$ if no stop occurs. Encode stops into the tagged state set $J=\mathrm{State}\sqcup(\{0,\dots,T\}\times\mathrm{State})$: the tagged step keeps stopped states fixed and moves a running state $j$ according to $\tau_t$, recording the stopping time. Give the tagged weight $w_n(j,\cdot)$ to running states and $w_t(a,\cdot)$ to stopped states $(t,a)$. If $n+k\le T$, the ordinary continuation $W$ over $J$ satisfies
--   $$
--   W_{n,k}(j,s)=\begin{cases}V_{n,k}(a,s),& j=a\text{ running},\\ w_t(a,s),& j=(t,a)\text{ stopped}.\end{cases}
--   $$
--
--   So the stopped continuation is the ordinary continuation of the tagged learner.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/StoppingKernel.lean#L318-L338

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
variable {d M T : ℕ}

theorem OAI.NoiselessRegression.Learner.continuation_tagged_eq {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (n k : ℕ) (hnk : n+k ≤ T) (j : TaggedState M T) (s : Vector d) :
    continuation (taggedStep τ) (taggedWeight w) n k j s =
      match j with
      | .inl a => stoppedContinuation τ w n k a s
      | .inr (t,a) => w t a s := by sorry
