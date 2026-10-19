-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_continuation_mass_bound_ceil
-- name    : OAI.NoiselessRegression.continuation_mass_bound_ceil
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:23:33.784548+00:00
-- url     : https://prove2.me/theorems/472b62b1-7421-4eec-ae72-aa05890e7b7b
-- title:
--   Polynomial mass bound for streaming continuations
-- statement:
--   For a finite state set $J$ and an integer $q\ge1$, the stream factor is $\Phi_q=32768^{\,n}\,|J|^{1/q}$, where $n=\dim E$. A measure $\mu$ has polynomial mass $(a,C)$ if $\mu(\bar B(z,r))\le C\,r^a$ for all $z$ and $r>0$. Given transition maps $\delta_t:J\times(E\times\mathbb R)\to J$ and weights $w_t(j,\cdot):E\to[0,1]$, the continuation $W_{n,k}(j,s)$ is the expected final weight after $k$ further Gaussian observations. It is defined by $W_{n,0}(j,s)=w_n(j,s)$ and $W_{n,k+1}(j,s)=\int W_{n+1,k}\bigl(\delta_{n+1}(j,(x,\langle s,x\rangle)),s\bigr)\,d\gamma(x)$, where $\gamma$ is the standard Gaussian on $E$. Let $\mu$ be a finite measure on $E$, $J$ nonempty, and suppose every $w_t(j,\cdot)\,\mu$ has polynomial mass $(a,C)$ with $0<C<\infty$. If $1\le n$, $a\le n$, $q\ge2$ and $2q\le a$, then for all $n_0$, $k$ and $j$,
--   $$
--   W_{n_0,k}(j,\cdot)\,\mu\ \text{has polynomial mass}\ \Bigl(a,\ C\,\Phi_q^{\lceil k/q\rceil}\Bigr).
--   $$
--
--   Each block of $q$ observations costs one factor of the stream factor.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Stopping.lean#L16-L75

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem OAI.NoiselessRegression.continuation_mass_bound_ceil [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ ((k+q-1)/q)) := by sorry
