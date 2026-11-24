-- Prove2me | Theorems.Thm_GaussianPerimeter_expLower_le_exp
-- name    : GaussianPerimeter.expLower_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:51.525986+00:00
-- url     : https://prove2.me/theorems/460df3a1-0d73-4670-bf4a-3db39baafa9f
-- title:
--   Gaussian Perimeter: exp Lower le exp
-- statement:
--   The Gaussian Perimeter construction uses the exp Lower le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/ExpBounds.lean#L221-L238
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/ExpBounds.lean#L221-L238

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GaussianPerimeter_ExpBounds
set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter
open ExpBounds

theorem GaussianPerimeter.expLower_le_exp (x : ℚ) : (expLower x : ℝ) ≤ Real.exp (x : ℝ) := by sorry
