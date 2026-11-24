-- Prove2me | Theorems.Thm_GaussianPerimeter_gaussianPrefactor_lower
-- name    : GaussianPerimeter.gaussianPrefactor_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:05:36.074821+00:00
-- url     : https://prove2.me/theorems/85c751fe-74bf-40db-87f9-5d6b434e0840
-- title:
--   Gaussian Perimeter: gaussian Prefactor lower
-- statement:
--   The prefactor in equation (14) for the paper's rational parameters.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Prefactor.lean#L16-L40
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Prefactor.lean#L16-L40

module
public import Definitions.Def_GaussianPerimeter_ExpBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Definitions.Def_GaussianPerimeter_Prefactor
set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter

theorem GaussianPerimeter.gaussianPrefactor_lower :
    (0.938393 : ℝ) ≤
      (2387 / 1000 : ℝ) * (6131 / 5000) *
        Real.exp (-((6131 / 5000 : ℝ) ^ 4) / 4) / Real.sqrt Real.pi := by sorry
