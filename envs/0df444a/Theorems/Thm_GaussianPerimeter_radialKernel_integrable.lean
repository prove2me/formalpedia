-- Prove2me | Theorems.Thm_GaussianPerimeter_radialKernel_integrable
-- name    : GaussianPerimeter.radialKernel_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:46:15.984898+00:00
-- url     : https://prove2.me/theorems/bd0ed92d-d5f8-4be0-ab8c-a3e685861417
-- title:
--   Gaussian Perimeter: radial Kernel integrable
-- statement:
--   The Gaussian Perimeter construction uses the radial Kernel integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L33-L41
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L33-L41

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

theorem GaussianPerimeter.radialKernel_integrable (n : ℕ) : Integrable (radialKernel n) := by sorry
