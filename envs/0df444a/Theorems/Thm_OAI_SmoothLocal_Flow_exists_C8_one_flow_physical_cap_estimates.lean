-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Flow_exists_C8_one_flow_physical_cap_estimates
-- name    : OAI.SmoothLocal.Flow.exists_C8_one_flow_physical_cap_estimates
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:32.61382+00:00
-- url     : https://prove2.me/theorems/88331c78-f792-49fa-9425-c47673e87ba1
-- title:
--   Physical-coordinate cap gradient estimate from $C^8$ bounds
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g=g_0+\eta$ be smooth and positive definite on an open set $U\supseteq S$, let $z$ be smooth on $U$, and suppose that on $S$ the derivatives through order $8$ of $g_{ij}$ are bounded by $G$, those of $z$ by $Z$, $|\det g|\ge d$, $|H_{yy}|\ge c$, $E\ge e_0$, $|q|\le 1/100$, and $z$ satisfies the Darboux equation $\det H=K_gE$. Suppose also that $g_0$ has the model curvature $\kappa(x^2-h(y))$ on $U$, that $\eta$ is supported in the patch box, and that $K_g<-\kappa/2$ on the central box.
--
--   Then there are an open set $V$ with $S\subseteq V\subseteq U$, on which $q$ is smooth with a $C^3$ bound depending only on $G,Z,d,c$, and a smooth flow chart $\Phi(t,s)=(t,Y(s,t))$ of $\partial_x-q\partial_y$ with positive transverse derivative, such that for every order $m$ and all $-2<L\le R<2$, $-2<\mathrm{bottom}\le\mathrm{top}<b\le0$,
--
--   $$\int_{\Phi(R_0)}\big(\partial_x\partial_y^{m+3}z\big)^2+\big(\partial_y^{m+4}z\big)^2\le C\Big(\int_{\Phi(R_1)}\mathcal R_m^2+\int_{\Phi(R_1)}\big(\partial_y^{m+3}z\big)^2\Big),$$
--
--   where $R_0=[L,R]\times[\mathrm{bottom},\mathrm{top}]$, $R_1$ is the enlarged rectangle up to the artificial edge $s=b$, $\mathcal R_m$ is the high remainder of the differentiated equation, and $C>0$ depends only on the listed bounds and the rectangle. This is the lower-cap gain of one derivative, stated in the original coordinates.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Flow.exists_C8_one_flow_physical_cap_estimates` in `lean/OAI/Geometry/IsometricImmersion/Caps/AllOrderPhysicalCap.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Caps/AllOrderPhysicalCap.lean; Section 3, Lemma 3.4 and Proposition 3.1

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem exists_C8_one_flow_physical_cap_estimates
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hzB : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1:ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (V : Set Coord) (Y : ℝ → ℝ → ℝ),
      IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (hessianQuotient (g0+eta) z) V ∧
      CoordinateBound (hessianQuotient (g0+eta) z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2:ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, Y s t ∈ Icc (-3:ℝ) 3) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, |Y s t-s| ≤ (1:ℝ)/50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50) ∧
      (∀ tl tr sb st : ℝ, closedRectangle tl tr sb st ⊆ capChartDomain →
        IsCompact (capChart Y '' closedRectangle tl tr sb st) ∧
        MeasurableSet (capChart Y '' closedRectangle tl tr sb st) ∧
        volume (capChart Y '' closedRectangle tl tr sb st) < ⊤ ∧
        capChart Y '' closedRectangle tl tr sb st ⊆ modelOpenSquare) ∧
      ∀ m : ℕ,
        (∀ p ∈ capChartDomain,
          multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
            (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
              capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
        ∀ L R bottom top b : ℝ,
          -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
          0 < heightPhysicalCapConstant G Z d c e0 kappa (m+3) L R bottom top b ∧
          (∫ p in capChart Y '' closedRectangle L R bottom top,
            (coordPartial 0 (verticalJet z (m+3)) p)^2+(verticalJet z (m+4) p)^2) ≤
            heightPhysicalCapConstant G Z d c e0 kappa (m+3) L R bottom top b*
              ((∫ p in capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b,
                  (actualHighRemainder (g0+eta) z m p)^2)+
                (∫ p in capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b,
                  (verticalJet z (m+3) p)^2)) := by
  sorry

end SmoothLocal.Flow
end
end OAI
