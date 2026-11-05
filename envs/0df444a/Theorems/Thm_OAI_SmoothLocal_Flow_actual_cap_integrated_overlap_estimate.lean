-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Flow_actual_cap_integrated_overlap_estimate
-- name    : OAI.SmoothLocal.Flow.actual_cap_integrated_overlap_estimate
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:59.627532+00:00
-- url     : https://prove2.me/theorems/3af63181-c8b4-4087-b392-0f4a5e346984
-- title:
--   Integrated directed estimate combining coercive and elliptic regions
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $u,f$ be smooth with $u_{tt}+Au_{ss}+Bu_t+Cu_s=f$ on the chart domain, $A=G_1K\circ\Phi$, with $g=g_0+\eta$ as before. Let $-2<L$, $R<2$, $-2<A_0\le b\le0$ and let $\epsilon,\lambda,c_1,c_2,\dots$ satisfy the listed budgets, with pointwise coercivity of the multiplier form with constant $c_2$ on the part $K\le c_1(b-s)$ of the integration region. With $D$ the distance bound and $I$ the primitive of $B$,
--
--   $$\frac{c_2}2\iint\chi^2\mathcal W(u_t^2+u_s^2)\le\Big(\frac{5}{2c_2}D^8e^{2\lambda+M_I}+C_oD^6\Big)\iint f^2+C_o(D^6+H_e)\iint u^2,$$
--
--   integrals taken over the enlarged rectangle up to $s=b$, where $C_o$ and $H_e$ are explicit budgets for the overlap and elliptic parts.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Flow.actual_cap_integrated_overlap_estimate` in `lean/OAI/Geometry/IsometricImmersion/Caps/IntegratedCapOverlap.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Caps/IntegratedCapOverlap.lean; Section 3.2, combining (3.16) and (3.19)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem actual_cap_integrated_overlap_estimate
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A0 b kappa c1 c2 glow lambda epsilon MI M MK : ℝ}
    {G1 B C I u f : Coord → ℝ}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0) (hAb : A0 ≤ b) (hb : b ≤ 0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hc2 : 0 < c2) (hg : 0 < glow)
    (hM : 0 ≤ M) (hMK : 0 ≤ MK) (hlambda : 0 ≤ lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hK : ContDiffOn ℝ ∞ (capPullback Y (gaussianCurvature (g0+eta))) capChartDomain)
    (hG1 : ContDiffOn ℝ ∞ G1 capChartDomain) (hB : ContDiffOn ℝ ∞ B capChartDomain)
    (hC : ContDiffOn ℝ ∞ C capChartDomain) (hI : ContDiffOn ℝ ∞ I capChartDomain)
    (hu : ContDiffOn ℝ ∞ u capChartDomain)
    (hEq : ∀ p ∈ capChartDomain,
      multiplierOperator (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C u p = f p)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox)
    (himage : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      capChart Y p ∈ U)
    (hdisp : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hIv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |I p| ≤ MI)
    (hIi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hGlow : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, glow ≤ G1 p)
    (hAv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      |G1 p*capPullback Y (gaussianCurvature (g0+eta)) p| ≤ M)
    (hAi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p| ≤ M)
    (hBv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |B p| ≤ M)
    (hCv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |C p| ≤ M)
    (hKi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0+eta))) p| ≤ MK)
    (hcoercive : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      capPullback Y (gaussianCurvature (g0+eta)) p ≤ c1*edgeDistance b p →
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C
          (directedM b lambda I) (directedN b lambda epsilon I) u p) :
    let D := capDistanceBound A0 b
    let COverlap := capOverlapEnergyCost L R A0 b kappa c1 c2 glow M lambda MI
    let HElliptic := capEllipticRatioBudget L R A0 b kappa c1 glow MK M
    (c2/2)*rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b
      (directedGradientEnergy (capSpatialCutoff L R A0) I u b lambda) ≤
      ((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b (fun p => (f p)^2) +
      (COverlap*(D^6+HElliptic))*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b (fun p => (u p)^2) := by
  sorry

end SmoothLocal.Flow
end
end OAI
