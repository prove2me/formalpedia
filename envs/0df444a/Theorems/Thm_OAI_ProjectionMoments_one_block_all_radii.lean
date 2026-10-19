-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_one_block_all_radii
-- name    : OAI.ProjectionMoments.one_block_all_radii
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:23:01.578024+00:00
-- url     : https://prove2.me/theorems/835bf751-7c37-481c-a5eb-c06a974c61aa
-- title:
--   Ball-mass bound for one fractional block at all radii
-- statement:
--   There is $C\ge1$ such that the following holds for all $d\ge16$, with $k=\lfloor d/4\rfloor$ and $\beta=d-1-k$. Let $\sigma$ be the normalized surface measure on the unit sphere of $\mathbb R^d$. Let $f_1,\dots,f_N$ be measurable densities with $0\le f_j\le1$, and $K\ge0$, such that each $f_j\,\sigma$ satisfies $f_j\sigma(\bar B(b,t))\le Kt^\beta$ for all balls. Let $Q_1,\dots,Q_N$ be measurable kernels on $(\mathbb R^d)^k\times\mathbb R^k$ with $\sum_jQ_j\le1$, and define the fractional block
--   $$
--   F(s)=\int\sum_{j=1}^NQ_j\bigl(X,(\langle s,X_i\rangle)_i\bigr)\,f_j(s)\,d\gamma^{\otimes k}(X).
--   $$
--   Then $F\sigma(\bar B(b,t))\le C^d\,N^{1/k}\,K\,t^\beta$ for all balls.
--
--   Combining $N$ pieces through a fractional partition costs only a factor $N^{1/k}$ in the ball-mass constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/AllRadii.lean#L138-L207

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.one_block_all_radii :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ N : ℕ, ∀ f : Fin N → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      (∀ j, Measurable (f j)) → (∀ j s, f j s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ j, AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (f j)) K β) →
      ∀ Q : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (Q j)) → (∀ z, ∑ j, Q j z ≤ 1) →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity (fractionalBlock Q f))
        (C^d*(N:ℝ)^(1/(k:ℝ))*K) β := by sorry
