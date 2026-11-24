-- Prove2me | Theorems.Thm_GaussianPerimeter_tendsto_floor_mul_scale
-- name    : GaussianPerimeter.tendsto_floor_mul_scale
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:13:09.556236+00:00
-- url     : https://prove2.me/theorems/bd3b4edb-f83a-4e5c-9dbd-f5b0f5822df5
-- title:
--   Gaussian Perimeter: tendsto floor mul scale
-- statement:
--   The integer part of a growing trial count preserves its product with the vanishing scale.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Basic.lean#L15-L26
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Basic.lean#L15-L26

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

theorem GaussianPerimeter.tendsto_floor_mul_scale {s : ℕ → ℝ} {b : ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < s n) (hb : 0 ≤ b) :
    Tendsto (fun n => (⌊b / s n⌋₊ : ℝ) * s n) atTop (𝓝 b) := by sorry
