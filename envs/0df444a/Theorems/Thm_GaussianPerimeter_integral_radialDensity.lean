-- Prove2me | Theorems.Thm_GaussianPerimeter_integral_radialDensity
-- name    : GaussianPerimeter.integral_radialDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:23:56.851036+00:00
-- url     : https://prove2.me/theorems/c95edeae-868d-4a17-8f42-c9717c0603b2
-- title:
--   Gaussian Perimeter: integral radial Density
-- statement:
--   The Gaussian Perimeter construction uses the integral radial Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L81-L84
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L81-L84

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

theorem GaussianPerimeter.integral_radialDensity (n : ℕ) (hn : 0 < n) :
    (∫ r : ℝ, radialDensity n r) = 1 := by sorry
