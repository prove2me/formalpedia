-- Prove2me | Theorems.Thm_GaussianPerimeter_gaussianLowerBound_numeric
-- name    : GaussianPerimeter.gaussianLowerBound_numeric
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:10:25.477+00:00
-- url     : https://prove2.me/theorems/0a81f1bc-d2ae-47da-98e6-a95faa54a5c4
-- title:
--   Gaussian Perimeter: gaussian Lower Bound numeric
-- statement:
--   The numerical lower bound in Theorem 1 for the parameters in equation (14).
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/QuadratureCertificate.lean#L146-L152
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/QuadratureCertificate.lean#L146-L152

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

theorem GaussianPerimeter.gaussianLowerBound_numeric :
    (0.31258 : ℝ) ≤ (B * A * Real.exp (-A ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ x in (-6 : ℝ)..6, Real.exp (-x ^ 2 - B * Real.exp (A ^ 2 * x))) := by sorry
