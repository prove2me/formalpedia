-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_Learner_stoppedContinuation_mass_bound
-- name    : OAI.NoiselessRegression.Learner.stoppedContinuation_mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:39:10.69758+00:00
-- url     : https://prove2.me/theorems/02b0a4a8-d99b-4de8-aa30-5ffaf9a29744
-- title:
--   Polynomial mass bound for stopped streaming continuations
-- statement:
--   Let $\tau_t:\mathrm{State}\times(\mathbb R^d\times\mathbb R)\to\{\text{stop},\text{continue}\}\times\mathrm{State}$ be stopping transitions on $2^M$ states and $w_t(j,\cdot)\in[0,1]$ weights on $\mathbb R^d$. The stopped continuation is defined by $V_{n,0}(j,s)=w_n(j,s)$ and $V_{n,k+1}(j,s)=\int\bigl[\text{if }\tau_{n+1}(j,(x,\langle s,x\rangle))=(\text{stop},a)\text{ then }w_{n+1}(a,s)\text{ else }V_{n+1,k}(a,s)\bigr]\,d\gamma(x)$. It is the expected weight at the stopping time, or at time $n+k$ if no stop occurs. Here $\Phi_q=32768^{\,d}\,\bigl(2^M(q+2)\bigr)^{1/q}$ is the stream factor of the locally tagged state set (states together with a stopping position inside a block of length $q$). Let $\sigma$ be the normalized surface measure on the unit sphere of $\mathbb R^d$. Suppose the $\tau_t$ and $w_t$ are measurable and every $w_t(j,\cdot)\,\sigma$ satisfies $\sigma_w(\bar B(z,r))\le Cr^a$ with $0<C<\infty$. If $1\le d$, $a\le d$, $q\ge2$ and $2q\le a$, then for all $n$, $k$, $j$ and all balls,
--   $$
--   V_{n,k}(j,\cdot)\,\sigma\bigl(\bar B(z,r)\bigr)\le C\,\Phi_q^{\lceil k/q\rceil}\,r^a .
--   $$
--
--   Stopping only costs a tag recording where in the current block the stop happened.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/StoppingKernel.lean#L228-L304

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
variable {d M : ℕ}

theorem OAI.NoiselessRegression.Learner.stoppedContinuation_mass_bound {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (ambientSphereLaw.withDensity (w n j)) a C)
    (hd : 1 ≤ d) (ha : a ≤ d) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (n k : ℕ) (j : State M) :
    PolynomialMass (ambientSphereLaw.withDensity (stoppedContinuation τ w n k j)) a
      (C * streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((k+q-1)/q)) := by sorry
