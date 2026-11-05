-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Flow_capFlowHeight_coordinate_bound
-- name    : OAI.SmoothLocal.Flow.capFlowHeight_coordinate_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:55.018391+00:00
-- url     : https://prove2.me/theorems/ae4b4b12-c730-4eff-b987-9e95b1c21d35
-- title:
--   Coordinate derivative bounds for the flow height
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $q$ be smooth on an open $U\supseteq S$ with $|q|\le1/100$ on $S$ and with $M\ge0$ bounding its coordinate derivatives on $S$ through the order fixed in the hypotheses. Let $Y$ be a continuous flow on $[-2,2]^2$ with values in $[-3,3]$, $Y(s,0)=s$ and $\partial_tY(s,t)=-q(t,Y(s,t))$. Then the flow height $(t,s)\mapsto Y(s,t)$ has all coordinate derivatives of order at most $3$ on the chart domain bounded by the explicit constant
--
--   $$\mathrm{flowCoordinateBound}(M),$$
--
--   which is a polynomial in $M$ and $e^{2M},e^{4M},e^{6M}$. This gives the low-order chart bounds used throughout Section 3.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Flow.capFlowHeight_coordinate_bound` in `lean/OAI/Geometry/IsometricImmersion/Caps/CapFlowJetBounds.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Caps/CapFlowJetBounds.lean; Section 3, the bounds after (3.4)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
variable (hM : 0 ≤ M)
variable (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
variable (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
variable (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
variable (hq3 : ∀ i j k : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j (coordPartial k q)) p| ≤ M)
include hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3

theorem capFlowHeight_coordinate_bound :
    CoordinateBound (capFlowHeight Y) capChartDomain 3 (flowCoordinateBound M) := by
  sorry

end ActualFlow
end SmoothLocal.Flow
end
end OAI
