-- Prove2me | Theorems.Thm_GaussianPerimeter_lowerBound_trapezoidal_error
-- name    : GaussianPerimeter.lowerBound_trapezoidal_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:05:29.680983+00:00
-- url     : https://prove2.me/theorems/ec49a1ae-e7ee-479d-9a90-e8a572419431
-- title:
--   Gaussian Perimeter: lower Bound trapezoidal error
-- statement:
--   The trapezoidal rule error for the numerical lower bound.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Quadrature.lean#L128-L144
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Quadrature.lean#L128-L144

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GaussianPerimeter_Quadrature
set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped Interval
open GaussianPerimeter
local notation "a₀" => (6131 / 5000 : ℝ)
local notation "b₀" => (2387 / 1000 : ℝ)
local notation "F" => lowerBoundIntegrand a₀ b₀

theorem GaussianPerimeter.lowerBound_trapezoidal_error :
    |trapezoidal_error F 10240 (-(15 / 4)) (5 / 4)| ≤ (0.00000219 : ℝ) := by sorry
