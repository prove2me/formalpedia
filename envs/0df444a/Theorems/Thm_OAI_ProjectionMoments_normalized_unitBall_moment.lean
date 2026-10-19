-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_normalized_unitBall_moment
-- name    : OAI.ProjectionMoments.normalized_unitBall_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:06:27.779056+00:00
-- url     : https://prove2.me/theorems/639ec316-cd07-4bca-be2e-f10ce173368a
-- title:
--   Unit-ball moment bound for normalized projection densities
-- statement:
--   For every $D>0$ there is $C_D>0$ with the following property. Let $d\ge32$, $k=\lfloor d/16\rfloor$ and $\lambda=(d-1)/2$. Let $\nu$ be a finite measure on $\mathbb R^d$ of total mass at most $1$, supported in the closed unit ball, with $\nu(\bar B(b,t))\le D^dt^\lambda$ for all balls. Let $u$ be an orthonormal $k$-frame such that for almost every Gaussian $X$ the projection of $\nu$ onto the rows $\mathrm{polar}_u(X)$ is absolutely continuous. Then the normalized density $g(X,y)=V_k f_\nu(\mathrm{polar}_u(X),y)$ is measurable, satisfies $(V_k^{-1}\mathrm{vol})\cdot g(X,\cdot)=$ the projected law for almost every $X$, and vanishes for $\|y\|>1$. Moreover
--   $$
--   \int\!\!\int g(X,y)^k\,d\beta_k(y)\,d\gamma^{\otimes k}(X)\le e^{C_Ddk},
--   $$
--   where $\beta_k$ is the unit ball law of $\mathbb R^k$ and $\gamma$ is the standard Gaussian on $\mathbb R^d$.
--
--   One can take $C_D=\log\bigl(16384\max(D,1)\bigr)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/BallMoments.lean#L291-L340

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

theorem OAI.ProjectionMoments.normalized_unitBall_moment (D : ℝ) (hD : 0 < D) :
    ∃ C_D : ℝ, 0 < C_D ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let lam : ℝ := ((d:ℝ)-1)/2
      ∀ (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
        (u : Fin k → EuclideanSpace ℝ (Fin d)),
        ν Set.univ ≤ 1 → ν.support ⊆ Metric.closedBall 0 1 →
        AllBallMass ν (D^d) lam → Orthonormal ℝ u →
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) →
        Measurable (normalizedDensity ν k u) ∧
        (∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))),
          ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
            (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X))) ∧
        (∀ X y, 1 < ‖y‖ → normalizedDensity ν k u (X,y) = 0) ∧
        (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^k ∂unitBallLaw k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
          ENNReal.ofReal (Real.exp (C_D*d*k)) := by sorry
