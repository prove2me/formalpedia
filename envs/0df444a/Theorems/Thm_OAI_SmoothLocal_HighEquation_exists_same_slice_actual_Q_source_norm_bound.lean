-- Prove2me | Theorems.Thm_OAI_SmoothLocal_HighEquation_exists_same_slice_actual_Q_source_norm_bound
-- name    : OAI.SmoothLocal.HighEquation.exists_same_slice_actual_Q_source_norm_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:52.478027+00:00
-- url     : https://prove2.me/theorems/a1a38fb7-c81a-4ea5-8835-553fa3a06b24
-- title:
--   $L^2$ bound on a slice for the remainder of the $Q$-equation
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Fix $G,R,Z$, a length floor and width, $H\ge0$, $d,c>0$ and $m$ with $m+3\ge8$. There is $B\ge0$ such that for all $g,z$ smooth on an open $U$, $S\subseteq U$, with $H_{xx}\ne0$ on $U$, and on $S$: coordinates bounded by $R$, horizontal two-jet of $g$ of order $m+3$ bounded by $G$, $C^3$ bound $Z$ for $z$, $|\det g|\ge d$, $|H_{xx}|\ge c$; for every horizontal segment at height $\theta$ in $S$ with length between the floor and the width, if the first-jet slice bound of order $m+2$ with constant $H$ holds, then
--
--   $$\Big(\int_\ell^r\mathcal R^Q_m(x,\theta)^2\,dx\Big)^{1/2}\le B.$$
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.HighEquation.exists_same_slice_actual_Q_source_norm_bound` in `lean/OAI/Geometry/IsometricImmersion/Energy/LocalQResidualL2.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Energy/LocalQResidualL2.lean; Section 4.2

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_same_slice_actual_Q_source_norm_bound
    (G R Z lengthFloor width : ℝ) (H : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hlen : 0 < lengthFloor)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ B : ℝ≥0, ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ U, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ theta left right : ℝ,
      (∀ x ∈ Icc left right, coordinatePoint x theta ∈ S) →
      lengthFloor ≤ right - left → right - left ≤ width →
      SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H →
      Real.sqrt (∫ x in left..right, actualQHighRemainder g z m (coordinatePoint x theta)^2) ≤ (B : ℝ) := by
  sorry

end SmoothLocal.HighEquation
end
end OAI
