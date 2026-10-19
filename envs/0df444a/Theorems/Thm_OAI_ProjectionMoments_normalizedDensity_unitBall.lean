-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_normalizedDensity_unitBall
-- name    : OAI.ProjectionMoments.normalizedDensity_unitBall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:15:14.786097+00:00
-- url     : https://prove2.me/theorems/9d51a905-0d95-48e5-81e4-90b2b73122c5
-- title:
--   The normalized density is a density for the unit ball law
-- statement:
--   For Gaussian rows $X=(X_1,\dots,X_k)$ in $E$ and an orthonormal $k$-frame $u$, let $\mathrm{polar}_u(X)$ be the polar normalization of $X$ (with fallback $u$ when the rows are dependent). The normalized density is $g(X,y)=V_k\,f_\nu(\mathrm{polar}_u(X),y)$, where $V_k$ is the volume of the closed unit ball of $\mathbb R^k$ and $f_\nu(A,\cdot)$ is the lower density of the projection $x\mapsto(\langle x,A_i\rangle)_i$ of $\nu$. The unit ball law $\beta_k$ is Lebesgue measure on the closed unit ball divided by $V_k$. Let $\nu$ be a finite measure on $E$ supported in the closed unit ball, $u$ an orthonormal $k$-frame, and $X$ such that the projection of $\nu$ onto the rows $\mathrm{polar}_u(X)$ is absolutely continuous. Then
--   $$
--   g(X,\cdot)\,\beta_k=\bigl(y\mapsto(\langle y,\mathrm{polar}_u(X)_i\rangle)_i\bigr)_*\nu .
--   $$
--
--   So $g(X,\cdot)$ is the density of the projected law with respect to the unit ball law.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/CapDuality.lean#L44-L59

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.normalizedDensity_unitBall (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (hac : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    (unitBallLaw k).withDensity (fun y => normalizedDensity ν k u (X,y)) =
      ν.map (rowMap (polarRows u X)) := by sorry
