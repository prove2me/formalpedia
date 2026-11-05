-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Flow_exists_uniform_original_data_actual_high_cap_estimate
-- name    : OAI.SmoothLocal.Flow.exists_uniform_original_data_actual_high_cap_estimate
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:29.5006+00:00
-- url     : https://prove2.me/theorems/6aee0806-e422-41cc-ab66-615796aafd91
-- title:
--   Directed gradient estimate on caps in flow coordinates, with constants from the original data
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g=g_0+\eta$ be smooth and positive on an open $U\supseteq S$, and $z$ smooth, with $C^4$ bound $G$ for $g$, $C^5$ bound $Z$ for $z$, $|\det g|\ge d$, $|H_{yy}|\ge c$, $E\ge e_0$, $|q|\le1/100$ and $\det H=KE$ on $S$; suppose $g_0$ has model curvature with $\kappa>0$, $\eta$ is supported in the patch box, and $K<-\kappa/2$ on the central box. Then for each $m$ there are positive constants $\epsilon\le1,\lambda,c_1,c_2$ depending only on these bounds and on $m$, and a smooth flow $Y$ with $Y(s,0)=s$ and $\partial_tY=-q$, such that $u=\partial_y^{m+3}z$ in the chart solves
--
--   $$u_{tt}+Au_{ss}+Bu_t+Cu_s=\mathcal R_m,$$
--
--   and for all $-2<L\le R<2$, $-2<\mathrm{bottom}\le\mathrm{top}<b\le0$,
--
--   $$\iint_{[L,R]\times[\mathrm{bottom},\mathrm{top}]}u_t^2+u_s^2\le\mathrm{RHS}(u,\mathcal R_m),$$
--
--   with an explicit right side given by $L^2$ integrals of $u$ and $\mathcal R_m$ on an enlarged rectangle.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Flow.exists_uniform_original_data_actual_high_cap_estimate` in `lean/OAI/Geometry/IsometricImmersion/Caps/UniformOriginalDataCapEstimate.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Caps/UniformOriginalDataCapEstimate.lean; Section 3.2, Lemma 3.4 and (3.12)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem exists_uniform_original_data_actual_high_cap_estimate
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => (g0+eta) p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1 : ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) (m : ℕ) :
    let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
    let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
    let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
    let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
    ∃ Y : ℝ → ℝ → ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) ∧
      (∀ p ∈ capChartDomain,
        multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
          (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
            capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
      ∀ L R bottom top b : ℝ,
        -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
        rectangleIntegral L R bottom top
          (fun p => (coordPartial 0 (capPullback Y (verticalJet z (m+3))) p)^2+
            (coordPartial 1 (capPullback Y (verticalJet z (m+3))) p)^2) ≤
          heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
            (capPullback Y (verticalJet z (m+3))) (capPullback Y (actualHighRemainder (g0+eta) z m)) := by
  sorry

end SmoothLocal.Flow
end
end OAI
