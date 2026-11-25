-- Prove2me | Theorems.Thm_FrontierMathLean_add_inv_mono_on_one
-- name    : FrontierMathLean.add_inv_mono_on_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:23.726739+00:00
-- url     : https://prove2.me/theorems/c41cdc9e-53df-4af1-bb39-12027a1339c1
-- title:
--   Frontier Math Lean: add inv mono on one
-- statement:
--   For positive `x` and `r`, if `1 ≤ r ≤ x`, then
--   `x + x⁻¹ ≥ r + r⁻¹`.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/AbstractInequality.lean#L15-L28
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/AbstractInequality.lean#L15-L28

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Definitions.Def_FrontierMathLean_AbstractInequality
set_option autoImplicit false
open FrontierMathLean

theorem FrontierMathLean.add_inv_mono_on_one
    {x r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) :
    r + r⁻¹ ≤ x + x⁻¹ := by sorry
