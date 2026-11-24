-- Prove2me | Theorems.Thm_GaussianPerimeter_volume_le_diameter_ball
-- name    : GaussianPerimeter.volume_le_diameter_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:35:42.204174+00:00
-- url     : https://prove2.me/theorems/45134bd5-e659-4013-b8b9-cad548e6312e
-- title:
--   Gaussian Perimeter: volume le diameter ball
-- statement:
--   The Euclidean isodiametric bound for compact sets. Apply Brunn–Minkowski
--   to a set and its reflection, whose sum fits in the ball of radius its diameter.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/HausdorffNormalization.lean#L15-L40
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/HausdorffNormalization.lean#L15-L40

module
public import Definitions.Def_GaussianPerimeter_BrunnMinkowski
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Definitions.Def_GaussianPerimeter_HausdorffNormalization
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Metric
open scoped ENNReal Pointwise
open GaussianPerimeter

theorem GaussianPerimeter.volume_le_diameter_ball {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hA : IsCompact A) :
    (2 : ℝ≥0∞) ^ (n + 1) * volume A ≤
      volume (closedBall 0 (diam A) : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by sorry
