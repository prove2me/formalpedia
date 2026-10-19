-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_stopped_route_mixed_bound
-- name    : OAI.NoiselessRegression.Learner.stopped_route_mixed_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-18T18:41:52.116977+00:00
-- url     : https://prove2.me/theorems/bca7ea8b-6e32-4676-8594-d78362a92f31
-- title:
--   Hitting bound for stopped streaming routes
-- statement:
--   Let $\tau_t:\mathrm{State}\times(\mathbb R^d\times\mathbb R)\to\{\text{stop},\text{continue}\}\times\mathrm{State}$ be stopping transitions on $2^M$ states and $w_t(j,\cdot)\in[0,1]$ weights on $\mathbb R^d$. The stopped continuation is defined by $V_{n,0}(j,s)=w_n(j,s)$ and $V_{n,k+1}(j,s)=\int\bigl[\text{if }\tau_{n+1}(j,(x,\langle s,x\rangle))=(\text{stop},a)\text{ then }w_{n+1}(a,s)\text{ else }V_{n+1,k}(a,s)\bigr]\,d\gamma(x)$. It is the expected weight at the stopping time, or at time $n+k$ if no stop occurs. Here $\Phi_q=32768^{\,d}\,\bigl(2^M(q+2)\bigr)^{1/q}$ is the stream factor of the locally tagged state set (states together with a stopping position inside a block of length $q$). Let $y_t:\mathrm{State}\to\mathbb R^d$ be target maps, $0<\varepsilon\le1$, $b\ge0$ with $a+b\le d-1$, $q\ge2$ and $2q\le a$. Let $s$ be uniform on the unit sphere and the samples standard Gaussian. Let $j_T$ be the tagged state reached from $j$ after $T$ tagged steps, and let $y(j_T)$ be $y_T(a)$ if it is running in state $a$ and $y_t(a)$ if it stopped at time $t$ in state $a$. Then
--   $$
--   \Pr\bigl[\|s-y(j_T)\|\le\varepsilon\bigr]\le3\cdot4^d\,\varepsilon^b\,\Phi_q^{\lceil T/q\rceil}.
--   $$
--
--   The bound depends on $T$ only through the number of blocks, not through the global stopping-time tags.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/StoppingKernel.lean#L369-L436

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
variable [NeZero d]

theorem OAI.NoiselessRegression.Learner.stopped_route_mixed_bound {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (y : ℕ → State M → Vector d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (j : TaggedState M T) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | dist z.1.val
        (match streamRoute (taggedStep (T := T) τ) 0 T j (z.2,fun i => ⟪z.1.val,z.2 i⟫) with
        | .inl a => y T a
        | .inr (t,a) => y t a) ≤ ε} ≤
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by sorry
