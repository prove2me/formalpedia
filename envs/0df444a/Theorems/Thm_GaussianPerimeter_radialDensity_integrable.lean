-- Prove2me | Theorems.Thm_GaussianPerimeter_radialDensity_integrable
-- name    : GaussianPerimeter.radialDensity_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:23:40.915812+00:00
-- url     : https://prove2.me/theorems/4524989f-0e04-44b9-9fff-d40f976fef7d
-- title:
--   Gaussian Perimeter: radial Density integrable
-- statement:
--   The Gaussian Perimeter construction uses the radial Density integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L69-L72
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L69-L72

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

theorem GaussianPerimeter.radialDensity_integrable (n : ℕ) : Integrable (radialDensity n) := by sorry
