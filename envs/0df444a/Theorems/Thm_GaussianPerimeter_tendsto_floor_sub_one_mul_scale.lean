-- Prove2me | Theorems.Thm_GaussianPerimeter_tendsto_floor_sub_one_mul_scale
-- name    : GaussianPerimeter.tendsto_floor_sub_one_mul_scale
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:13:16.2918+00:00
-- url     : https://prove2.me/theorems/0b1374ba-9417-457d-a951-ebcee96d40d0
-- title:
--   Gaussian Perimeter: tendsto floor sub one mul scale
-- statement:
--   Removing one trial has no effect on the scaled limit.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Basic.lean#L29-L46
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Basic.lean#L29-L46

module
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Order.LiminfLimsup
public import Definitions.Def_GaussianPerimeter_Basic
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter

theorem GaussianPerimeter.tendsto_floor_sub_one_mul_scale {s : ℕ → ℝ} {b : ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < s n) (hb : 0 ≤ b) :
    Tendsto (fun n => ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) * s n) atTop (𝓝 b) := by sorry
