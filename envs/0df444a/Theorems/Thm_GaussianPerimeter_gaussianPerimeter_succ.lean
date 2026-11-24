-- Prove2me | Theorems.Thm_GaussianPerimeter_gaussianPerimeter_succ
-- name    : GaussianPerimeter.gaussianPerimeter_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:53.699085+00:00
-- url     : https://prove2.me/theorems/44d24b8d-364d-4117-9be1-8ee007eb8333
-- title:
--   Gaussian Perimeter: gaussian Perimeter succ
-- statement:
--   The perimeter formula in positive dimension.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Definitions.lean#L30-L36
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Definitions.lean#L30-L36

module
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Definitions.Def_GaussianPerimeter_Definitions
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal
open GaussianPerimeter

theorem GaussianPerimeter.gaussianPerimeter_succ (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin (k + 1)))) :
    gaussianPerimeter K =
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) / (2 : ℝ≥0∞) ^ k) *
        (∫⁻ x in frontier K, ENNReal.ofReal
          ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2)) ∂μH[(k : ℝ)]) := by sorry
