-- Prove2me | Theorems.Thm_GaussianPerimeter_lowerBound_integral
-- name    : GaussianPerimeter.lowerBound_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:08:32.518722+00:00
-- url     : https://prove2.me/theorems/ae6ebab8-c452-4f66-94e5-04c3b82981a9
-- title:
--   Gaussian Perimeter: lower Bound integral
-- statement:
--   Certified numerical lower bound for the integral in Theorem 1, equation (14).
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/QuadratureCertificate.lean#L114-L143
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/QuadratureCertificate.lean#L114-L143

module
public import Definitions.Def_GaussianPerimeter_Quadrature
public import Definitions.Def_GaussianPerimeter_Prefactor
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GaussianPerimeter_QuadratureCertificate
set_option autoImplicit true
@[expose] public section
public section
open Finset
open GaussianPerimeter
local notation "A" => (6131 / 5000)
local notation "B" => (2387 / 1000)
local notation "F" => lowerBoundIntegrand A B

theorem GaussianPerimeter.lowerBound_integral :
    (0.333104 : ℝ) ≤ ∫ x in (-6 : ℝ)..6, F x := by sorry
