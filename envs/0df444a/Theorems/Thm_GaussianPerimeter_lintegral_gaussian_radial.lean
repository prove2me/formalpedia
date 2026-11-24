-- Prove2me | Theorems.Thm_GaussianPerimeter_lintegral_gaussian_radial
-- name    : GaussianPerimeter.lintegral_gaussian_radial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:57:35.779737+00:00
-- url     : https://prove2.me/theorems/70f34028-e90f-4545-adc5-c7590a62424e
-- title:
--   Gaussian Perimeter: lintegral gaussian radial
-- statement:
--   Radial integration against the normalized Gaussian density in positive dimension.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/RadialIntegration.lean#L70-L119
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/RadialIntegration.lean#L70-L119

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

theorem GaussianPerimeter.lintegral_gaussian_radial (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫⁻ x : Euc (n + 1), ENNReal.ofReal
      ((2 * Real.pi) ^ (-((n + 1 : ℕ) : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2) * f ‖x‖)) =
      ∫⁻ r : ℝ, ENNReal.ofReal (radialDensity (n + 1) r * f r) := by sorry
