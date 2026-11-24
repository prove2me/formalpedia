-- Prove2me | Theorems.Thm_GaussianPerimeter_radialDensity_measurable
-- name    : GaussianPerimeter.radialDensity_measurable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:09:32.705645+00:00
-- url     : https://prove2.me/theorems/238726a8-18de-4dcf-98a1-6a20b031755d
-- title:
--   Gaussian Perimeter: radial Density measurable
-- statement:
--   The Gaussian Perimeter construction uses the radial Density measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L74-L79
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L74-L79

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

theorem GaussianPerimeter.radialDensity_measurable (n : ℕ) : Measurable (radialDensity n) := by sorry
