-- Prove2me | Theorems.Thm_GaussianPerimeter_lintegral_norm_euclidean
-- name    : GaussianPerimeter.lintegral_norm_euclidean
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:57:33.591803+00:00
-- url     : https://prove2.me/theorems/3c175ad4-ca29-42c8-9d2d-b94ea8c48013
-- title:
--   Gaussian Perimeter: lintegral norm euclidean
-- statement:
--   The radial form of a nonnegative integral on Euclidean space.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/RadialIntegration.lean#L17-L46
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/RadialIntegration.lean#L17-L46

module
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Definitions.Def_GaussianPerimeter_RadialIntegration
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped ENNReal Topology
open GaussianPerimeter
local notation "Euc" => fun n => EuclideanSpace ℝ (Fin n)

theorem GaussianPerimeter.lintegral_norm_euclidean (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Euc (n + 1), f ‖x‖) =
      ((n + 1 : ℕ) : ℝ≥0∞) * volume (Metric.ball (0 : Euc (n + 1)) 1) *
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * f r) := by sorry
