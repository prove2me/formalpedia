-- Prove2me | Theorems.Thm_GaussianPerimeter_tendsto_radialDensity_shift
-- name    : GaussianPerimeter.tendsto_radialDensity_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:51:09.292235+00:00
-- url     : https://prove2.me/theorems/e21e8850-e6e7-4ae2-b506-baf96d3565e3
-- title:
--   Gaussian Perimeter: tendsto radial Density shift
-- statement:
--   Lemma 10 in the pointwise form needed for the lower bound on Gaussian perimeter.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L233-L238
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Radial.lean#L233-L238

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

theorem GaussianPerimeter.tendsto_radialDensity_shift (w : ℝ) :
    Tendsto (fun n => radialDensity n (Real.sqrt ((n - 1 : ℕ) : ℝ) + w))
      atTop (𝓝 (Real.exp (-w ^ 2) / Real.sqrt Real.pi)) := by sorry
