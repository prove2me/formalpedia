-- Prove2me | Theorems.Thm_OAI_SmoothLocal_HighEquation_exists_Q_spatial_induction_step
-- name    : OAI.SmoothLocal.HighEquation.exists_Q_spatial_induction_step
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:57.636644+00:00
-- url     : https://prove2.me/theorems/ca1196c0-5bcf-48cc-aaf7-06e547721ca6
-- title:
--   One-derivative gain for the hyperbolic $Q$-equation on slices
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Fix slab data and $s_0,M,$ speed, $T$, a length floor below the slab width, $d,c>0$ and $m$ with $m+3\ge8$, together with slice bound $H$ and initial bound $A$. There is $H_{\mathrm{new}}\ge H$ such that for all $g,z$ smooth on a coordinate rectangle containing the slab, with $\det H=KE$, $H_{xx}\ne0$ on the rectangle, the low bounds for $Q$ with parameters $s_0,M$, speed on the slab, the metric derivatives through order $m+5$ bounded by $G$, $C^8$ bound $Z$ for $z$, $|\det g|\ge d$, $|H_{xx}|\ge c$, and all derivatives of $z$ through order $m+4$ at most $A$ on the initial cut: if the first-jet spatial slice bound of order $m+2$ with constant $H$ holds at all times, then the same bound of order $m+3$ with constant $H_{\mathrm{new}}$ holds at all times.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.HighEquation.exists_Q_spatial_induction_step` in `lean/OAI/Geometry/IsometricImmersion/Darboux/QSpatialInductionStep.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Darboux/QSpatialInductionStep.lean; Section 4.2, (4.15)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_Q_spatial_induction_step
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (H A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ Hnew : ℝ≥0, H ≤ Hnew ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (m + 5) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ m + 4 → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      (∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (m + 2) H) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (m + 3) Hnew := by
  sorry

end SmoothLocal.HighEquation
end
end OAI
