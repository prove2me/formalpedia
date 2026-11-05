-- Prove2me | Theorems.Thm_OAI_SmoothLocal_HighEquation_coordinateL2Bound_order_step
-- name    : OAI.SmoothLocal.HighEquation.coordinateL2Bound_order_step
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:38.361097+00:00
-- url     : https://prove2.me/theorems/63d63f55-eb71-4978-9d49-6d83f4a2974c
-- title:
--   Recovering all derivatives of order $N$ from the top $y$-derivatives
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $z$ be smooth on an open set $U$ and satisfy $\det H=KE$ with $H_{yy}\ne0$ there. Let $V\subseteq U\cap S$ be measurable, $N\ge7$, $C\ge0$, $B\ge1$. Suppose the derivatives through order $N-2$ of the six-variable function $P$ at the solution jet are bounded by $C$ on $V$, that $z$ has coordinate derivatives through order $N-3$ bounded by $B$ on $V$, that all derivatives of order at most $N-1$ have $L^2(V)$ norm at most $H$, and that $\partial_y^Nz$ and $\partial_x\partial_y^{N-1}z$ have $L^2(V)$ norm at most $H_{\mathrm{top}}$. Then all coordinate derivatives of $z$ of order at most $N$ have $L^2(V)$ norm at most an explicit budget depending only on $C,B,H,H_{\mathrm{top}},N$.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.HighEquation.coordinateL2Bound_order_step` in `lean/OAI/Geometry/IsometricImmersion/Estimates/RemainderAreaBudget.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Estimates/RemainderAreaBudget.lean; Section 3.3, the recovery step from (3.5)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Analytic

theorem coordinateL2Bound_order_step
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVS : V ⊆ modelSquare)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H Htop : ℝ≥0}
    (hP : ∀ n ≤ N-2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N-3) B)
    (hheight : CoordinateL2Bound z V (N-1) H)
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N-1))) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞)) :
    CoordinateL2Bound z V N (uniformMixedOrderBudget C B H Htop N) := by
  sorry

end SmoothLocal.HighEquation
end
end OAI
