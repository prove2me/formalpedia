-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_normalizedMoment_le
-- name    : OAI.ProjectionMoments.normalizedMoment_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:02:55.102449+00:00
-- url     : https://prove2.me/theorems/2566db78-d7e8-46f9-aad1-a5d76aa45a89
-- title:
--   Normalized density moments are bounded by frame label moments
-- statement:
--   For Gaussian rows $X=(X_1,\dots,X_k)$ in $E$ and an orthonormal $k$-frame $u$, let $\mathrm{polar}_u(X)$ be the polar normalization of $X$ (with fallback $u$ when the rows are dependent). The normalized density is $g(X,y)=V_k\,f_\nu(\mathrm{polar}_u(X),y)$, where $V_k$ is the volume of the closed unit ball of $\mathbb R^k$ and $f_\nu(A,\cdot)$ is the lower density of the projection $x\mapsto(\langle x,A_i\rangle)_i$ of $\nu$. The unit ball law $\beta_k$ is Lebesgue measure on the closed unit ball divided by $V_k$. Let $\nu$ be a finite measure on $E$, $k\le\dim E$, and $u$ an orthonormal $k$-frame. Then for every $n'$,
--   $$
--   \int\!\!\int g(X,y)^{n'+1}\,d\beta_k(y)\,d\gamma^{\otimes k}(X)\le V_k^{\,n'}\int\mathrm{labelMoment}_{n'}(A)\,d\mathrm{frame}_u(A),
--   $$
--   where $\mathrm{labelMoment}_{n'}(A)=\int f_\nu(A,y)^{n'+1}\,dy$ and $\gamma$ is the standard Gaussian on $E$.
--
--   So moments with respect to the unit ball law reduce to the label moments of uniformly random frames.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/BallMoments.lean#L89-L108

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.normalizedMoment_le (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) {u : Fin k → E} (hu : Orthonormal ℝ u) (n : ℕ) :
    (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k
      ∂Measure.pi (fun _ => stdGaussian E)) ≤
      unitBallVolume k ^ n * ∫⁻ A, labelMoment ν k n A ∂frameLaw u := by sorry
