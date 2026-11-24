-- Prove2me | Theorems.Thm_GaussianPerimeter_integral_radialKernel
-- name    : GaussianPerimeter.integral_radialKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:36.261342+00:00
-- url     : https://prove2.me/theorems/853dcbf5-09f4-4985-81b4-310905733c4e
-- title:
--   Gaussian Perimeter: integral radial Kernel
-- statement:
--   The Gaussian Perimeter construction uses the integral radial Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L43-L59
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L43-L59

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

theorem GaussianPerimeter.integral_radialKernel (n : ℕ) (hn : 0 < n) :
    (∫ r : ℝ, radialKernel n r) =
      (1 / 2 : ℝ) ^ (-(n : ℝ) / 2) * (1 / 2) * Real.Gamma ((n : ℝ) / 2) := by sorry
