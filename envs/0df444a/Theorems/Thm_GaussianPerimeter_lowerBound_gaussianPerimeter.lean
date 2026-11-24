-- Prove2me | Theorems.Thm_GaussianPerimeter_lowerBound_gaussianPerimeter
-- name    : GaussianPerimeter.lowerBound_gaussianPerimeter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:05:41.815904+00:00
-- url     : https://prove2.me/theorems/1fb2db6c-bd20-4f38-b3b6-6bd623a9916d
-- title:
--   Gaussian Perimeter: lower Bound gaussian Perimeter
-- statement:
--   The asymptotic perimeter inequality before evaluating the numerical integral.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Construction.lean#L139-L143
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Construction.lean#L139-L143

module
public import Definitions.Def_GaussianPerimeter_Averaging
public import Definitions.Def_GaussianPerimeter_HausdorffNormalization
public import Definitions.Def_GaussianPerimeter_NazarovLimit
public import Definitions.Def_GaussianPerimeter_RadialIntegration
public import Definitions.Def_GaussianPerimeter_SphereCap
public import Definitions.Def_GaussianPerimeter_Construction
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace
open GaussianPerimeter

theorem GaussianPerimeter.lowerBound_gaussianPerimeter {a b W : ℝ} (ha : 0 < a) (hb : 0 < b) (hW : 0 ≤ W) :
    ENNReal.ofReal ((b * a * Real.exp (-a ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ w in (-W)..W, Real.exp (-w ^ 2 - b * Real.exp (a ^ 2 * w)))) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop := by sorry
