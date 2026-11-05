-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Flow_patch_actual_directed_near_coercivity
-- name    : OAI.SmoothLocal.Flow.patch_actual_directed_near_coercivity
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:54.799426+00:00
-- url     : https://prove2.me/theorems/77eb29c4-1540-4f4f-a554-9fc369c34deb
-- title:
--   Directed multiplier is coercive near and inside the negative curvature region
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g=g_0+\eta$ be smooth and positive on an open $U$, $z$ a smooth Darboux solution with $H_{yy}\ne0$, $E>0$ on $U$, and $Y$ the flow chart of $\partial_x-q\partial_y$ with positive transverse derivative, $|Y(s,t)-s|\le1/50$, $|q|\le1/100$ on $S$, chart image in $U$. Suppose $g_0$ has model curvature with $\kappa>0$, $\eta$ is supported in the patch box and $K<-\kappa/2$ on the central box. Let $p$ be in the chart domain with $s\le0$, let $\ell\in\mathbb N$, and suppose numerical budgets on $\epsilon,\lambda,c_1$ and bounds on the coefficients at $p$ hold, including that $K(p)\le c_1(\mathrm{edge}-s)$. Then for all real $x,y$,
--
--   $$\min\Big(\frac\lambda8,\frac{\mu}{4}\Big)W(p)(x^2+y^2)\le T(p)x^2+S_0(p)y^2+J(p)xy,$$
--
--   where $W$ is the directed weight, $T,S_0,J$ are the coefficients in (3.14), and $\mu$ is the model coercivity margin determined by $\kappa,\epsilon,\ell$ and the bounds for $G_1$ and $s_y$.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Flow.patch_actual_directed_near_coercivity` in `lean/OAI/Geometry/IsometricImmersion/Energy/PatchDirectedCoercivity.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Energy/PatchDirectedCoercivity.lean; Section 3.2, (3.16)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem patch_actual_directed_near_coercivity
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord}
    {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hDarboux : ∀ p ∈ U,
      (covHessian (g0 + eta) z p).det = gaussianCurvature (g0 + eta) p * heightEnergy (g0 + eta) z p)
    (hyy : ∀ p ∈ U, covHessian (g0 + eta) z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy (g0 + eta) z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    (cG rhoMax epsilon MG MI MB Mr MA MAs MG1 c1 D edge lambda : ℝ)
    (hkappa : 0 < kappa) (hcG : 0 < cG) (hG : cG ≤ heightChartG1 (g0 + eta) z Y p)
    (hrhoMax : capChartRho Y p ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hqbudget : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGs : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hGt : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hKsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (hIs : |coordPartial 1 (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤ MI)
    (hBp : |heightChartB (g0 + eta) z Y ell p| ≤ MB)
    (hr : |heightChartRemainder (g0 + eta) z Y ell p| ≤ Mr)
    (hAp : |heightChartA (g0 + eta) z Y p| ≤ MA)
    (hAs : |coordPartial 1 (heightChartA (g0 + eta) z Y) p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda)
    (hEbudget : (MI + 1 + 2 * MB) / 2 + Mr ≤ lambda / 8)
    (hcrossbudget : 4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 *
      epsilon^2 * MA ≤ 1 / 8)
    (hloss : (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
      modelCoercivityMargin cG kappa rhoMax epsilon ell / 8)
    (hGmax : heightChartG1 (g0 + eta) z Y p ≤ MG1)
    (hc1 : 0 ≤ c1) (hdist : edge - p 1 ≤ D)
    (hKstrip : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ c1 * (edge - p 1))
    (hstripbudget : MG1 * c1 * (lambda * D + 8) ≤
      modelCoercivityMargin cG kappa rhoMax epsilon ell / 6)
    (x y : ℝ) :
    let A := heightChartA (g0 + eta) z Y
    let B := heightChartB (g0 + eta) z Y ell
    let C := heightChartC (g0 + eta) z Y ell
    let I := coordinatePrimitive B
    min (lambda / 8) (modelCoercivityMargin cG kappa rhoMax epsilon ell / 4) *
      directedWeight edge lambda I p * (x^2 + y^2) ≤
      multiplierT B (directedM edge lambda I) (directedN edge lambda epsilon I) p * x^2 +
        multiplierS A C (directedM edge lambda I) (directedN edge lambda epsilon I) p * y^2 +
        multiplierJ A B C (directedM edge lambda I) (directedN edge lambda epsilon I) p * x * y := by
  sorry

end SmoothLocal.Flow
end
end OAI
