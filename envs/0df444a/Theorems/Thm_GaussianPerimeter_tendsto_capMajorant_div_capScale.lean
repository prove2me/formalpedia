-- Prove2me | Theorems.Thm_GaussianPerimeter_tendsto_capMajorant_div_capScale
-- name    : GaussianPerimeter.tendsto_capMajorant_div_capScale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:35:34.592629+00:00
-- url     : https://prove2.me/theorems/86a727d6-afd7-48b0-adc6-2f04d201204d
-- title:
--   Gaussian Perimeter: tendsto cap Majorant div cap Scale
-- statement:
--   The majorant has the normalized pointwise limit used in the Gaussian-perimeter argument.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L443-L556
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L443-L556

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter

theorem GaussianPerimeter.tendsto_capMajorant_div_capScale (a w : ℝ) (ha : 0 < a) :
    Tendsto (fun n => capMajorant a n w / capScale a n) atTop (𝓝 (Real.exp (a ^ 2 * w))) := by sorry
