-- Prove2me | Theorems.Thm_GaussianPerimeter_lowerBound_integral_of_trapezoidal
-- name    : GaussianPerimeter.lowerBound_integral_of_trapezoidal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:05:35.202805+00:00
-- url     : https://prove2.me/theorems/264940eb-65e7-4ac0-b691-7ab8274d7e62
-- title:
--   Gaussian Perimeter: lower Bound integral of trapezoidal
-- statement:
--   A lower estimate for the trapezoidal sum transfers to the integral in the paper.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Quadrature.lean#L147-L156
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Quadrature.lean#L147-L156

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

theorem GaussianPerimeter.lowerBound_integral_of_trapezoidal
    (h : (0.3331065 : ℝ) ≤ trapezoidal_integral F 10240 (-(15 / 4)) (5 / 4)) :
    (0.333104 : ℝ) ≤ ∫ x in (-6 : ℝ)..6, F x := by sorry
