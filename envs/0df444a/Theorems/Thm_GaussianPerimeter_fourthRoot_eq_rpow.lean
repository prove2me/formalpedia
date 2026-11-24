-- Prove2me | Theorems.Thm_GaussianPerimeter_fourthRoot_eq_rpow
-- name    : GaussianPerimeter.fourthRoot_eq_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:43:45.329807+00:00
-- url     : https://prove2.me/theorems/20b10bcb-fcda-4b68-8be4-eae695193809
-- title:
--   Gaussian Perimeter: fourth Root eq rpow
-- statement:
--   The Gaussian Perimeter construction uses the fourth Root eq rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Scaling.lean#L37-L40
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Scaling.lean#L37-L40

module
public import Definitions.Def_GaussianPerimeter_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_GaussianPerimeter_Scaling
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
open GaussianPerimeter

theorem GaussianPerimeter.fourthRoot_eq_rpow (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by sorry
