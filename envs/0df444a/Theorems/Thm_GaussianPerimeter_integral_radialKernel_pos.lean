-- Prove2me | Theorems.Thm_GaussianPerimeter_integral_radialKernel_pos
-- name    : GaussianPerimeter.integral_radialKernel_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:09:38.684806+00:00
-- url     : https://prove2.me/theorems/61cb9e84-0102-4917-bb21-ade77dc15343
-- title:
--   Gaussian Perimeter: integral radial Kernel pos
-- statement:
--   The Gaussian Perimeter construction uses the integral radial Kernel pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L61-L64
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L61-L64

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_GaussianPerimeter_Radial
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Topology
open GaussianPerimeter

theorem GaussianPerimeter.integral_radialKernel_pos (n : ℕ) (hn : 0 < n) :
    0 < ∫ r : ℝ, radialKernel n r := by sorry
