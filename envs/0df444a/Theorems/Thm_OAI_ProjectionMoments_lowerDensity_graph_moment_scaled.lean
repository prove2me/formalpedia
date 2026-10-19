-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_lowerDensity_graph_moment_scaled
-- name    : OAI.ProjectionMoments.lowerDensity_graph_moment_scaled
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:48:34.953275+00:00
-- url     : https://prove2.me/theorems/70098355-4f44-421f-b62d-ec96eaf90d89
-- title:
--   Gaussian moments of lower densities near the projected centre
-- statement:
--   For a measure $\nu$ on a finite-dimensional inner product space $E$ and rows $A=(A_1,\dots,A_m)$, the row map is $x\mapsto(\langle x,A_j\rangle)_j\in\mathbb R^m$; the ball average at $(A,y)$ with radius $\eta$ is the $\nu$-mass whose projection lies in $\bar B(y,\eta)$ divided by the volume of that ball, and the lower density is the $\liminf$ of ball averages along $\eta=1/(n+1)$. Let $\nu$ be finite with all-ball mass bound $\nu(\bar B(b,t))\le Kt^a$, $K>0$, and supported in $\bar B(z,R)$. If $q+m\le a$, then for every offset $b\in\mathbb R^m$,
--   $$
--   \int\underline f_\nu\bigl(A,\ (\langle z,A_j\rangle)_j+b\bigr)^q\,d\gamma^{\otimes m}(A)\le\Bigl(KR^{a-m}\bigl(1+3^n4^a2^{m+1}\bigr)\Bigr)^q ,
--   $$
--   where $n=\dim E$ and $A$ consists of $m$ independent Gaussian rows.
--
--   This is the basic Gaussian moment bound for projected densities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Graph.lean#L433-L452

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.lowerDensity_graph_moment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hmargin : (q : ℝ) + m ≤ a) (b : Label m) :
    ∫⁻ A : Fin m → E, (lowerDensity ν m (A, rowMap A z + b)) ^ q
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      (ENNReal.ofReal (K * R ^ (a-m)) *
        (1 + ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * (4 : ℝ)^a) *
          (2 : ℝ≥0∞)^(m+1))) ^ q := by sorry
