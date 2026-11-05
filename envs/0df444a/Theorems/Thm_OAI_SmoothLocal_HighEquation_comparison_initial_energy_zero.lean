-- Prove2me | Theorems.Thm_OAI_SmoothLocal_HighEquation_comparison_initial_energy_zero
-- name    : OAI.SmoothLocal.HighEquation.comparison_initial_energy_zero
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:32.574365+00:00
-- url     : https://prove2.me/theorems/9a00542a-6e49-40e0-9ad2-03dd5294aa0f
-- title:
--   Comparison energy vanishes on the initial cut
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $P,z$ be smooth on an open set $U$ containing the cut $\{(x,a):x\in(\ell,r)\}$, with $P=z$ and $\partial_yP=\partial_yz$ on this cut. For any function $S$ and $\ell<x_\ell\le x_r<r$,
--
--   $$\int_{x_\ell}^{x_r}\tfrac12\Big((\partial_yw)^2+S(\partial_xw)^2\Big)(x,a)\,dx=0,\qquad w=P-z.$$
--
--   This is the zero Cauchy data statement for the difference between the comparison function and the height.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.HighEquation.comparison_initial_energy_zero` in `lean/OAI/Geometry/IsometricImmersion/Comparison/ActualComparisonEquation.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Comparison/ActualComparisonEquation.lean; Section 4.3

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Taylor
open SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem comparison_initial_energy_zero
    {U : Set Coord} {P z S : Coord → ℝ} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U)
    {left right xl xr a : ℝ} (hlr : xl ≤ xr)
    (hcut : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, P (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right, coordPartial 1 P (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    (hxl : left < xl) (hxr : xr < right) :
    (∫ x in xl..xr, energyDensity S (comparisonDifference P z) (coordinatePoint x a)) = 0 := by
  sorry

end SmoothLocal.HighEquation
end
end OAI
