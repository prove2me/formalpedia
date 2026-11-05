-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Flow_exists_height_flow_uniform_coefficients
-- name    : OAI.SmoothLocal.Flow.exists_height_flow_uniform_coefficients
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:28:11.755455+00:00
-- url     : https://prove2.me/theorems/a5a67c56-7b93-433f-aab9-cdfd865f87be
-- title:
--   Flow chart of $\partial_x-q\partial_y$ with uniform coefficient bounds
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $z$ be smooth on $U$ with $C^5$ bound $Z$ on $S$, $|H_{yy}|\ge c$, $E\ge e_0$, $|q|\le1/100$ and $\det H=KE$ on $S$, with $G$, $d$ as before. There is $Y:\mathbb R^2\to\mathbb R$ such that the chart $\Phi(t,s)=(t,Y(s,t))$ is smooth on its domain, $Y(s,0)=s$, $\partial_tY(s,t)=-q(t,Y(s,t))$, $Y$ stays in $[-3,3]$ and $|Y(s,t)-s|\le1/50$ on $[-2,2]^2$, and $\partial_sY>0$ with an explicit two-sided bound by $e^{\pm2J}$ for the $C^1$ bound $J$ of $q$. Moreover the chart coefficients $A,B,C$ of the differentiated equation have explicit uniform $C^1$ bounds, $G_1\ge$ an explicit positive lower bound, and for every $\ell$,
--
--   $$C=(\ell+1)\partial_sA+A\,r_\ell,\qquad|r_\ell|\le\text{explicit bound},$$
--
--   which is the structure (3.10).
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Flow.exists_height_flow_uniform_coefficients` in `lean/OAI/Geometry/IsometricImmersion/Flows/HeightFlowUniformBounds.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Flows/HeightFlowUniformBounds.lean; Section 3, (3.3)-(3.4) and (3.10)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem exists_height_flow_uniform_coefficients
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy g z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    (hD : ∀ p ∈ modelSquare, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      (∀ p ∈ capChartDomain,
        0 < capChartRho Y p ∧
        1 / Real.exp (2 * heightQuotientJetBound G Z d c) ≤ capChartRho Y p ∧
        capChartRho Y p ≤ 1 / Real.exp (-2 * heightQuotientJetBound G Z d c)) ∧
      ContDiffOn ℝ ∞ (heightChartG1 g z Y) capChartDomain ∧
      CoordinateBound (heightChartG1 g z Y) capChartDomain 1 (heightG1JetBound G Z d c) ∧
      (∀ p ∈ capChartDomain, heightG1Lower G Z d c e0 ≤ heightChartG1 g z Y p) ∧
      (∀ ell : ℕ,
        ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain ∧
        CoordinateBound (heightChartB g z Y ell) capChartDomain 1 (heightBJetBound G Z d c ell) ∧
        ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain ∧
        ∀ p ∈ capChartDomain,
          |heightChartRemainder g z Y ell p| ≤ heightRemainderBound G Z d c e0 ell ∧
          heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
            heightChartA g z Y p * heightChartRemainder g z Y ell p) := by
  sorry

end SmoothLocal.Flow
end
end OAI
