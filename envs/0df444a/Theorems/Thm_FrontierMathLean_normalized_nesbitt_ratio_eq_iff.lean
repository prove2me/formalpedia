-- Prove2me | Theorems.Thm_FrontierMathLean_normalized_nesbitt_ratio_eq_iff
-- name    : FrontierMathLean.normalized_nesbitt_ratio_eq_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:36:36.178671+00:00
-- url     : https://prove2.me/theorems/8d0e8e3e-c263-413d-a6fe-5778f15c30ed
-- title:
--   Frontier Math Lean: normalized nesbitt ratio eq iff
-- statement:
--   Equality in the normalized ratio-constrained Nesbitt inequality occurs
--   exactly when both variables attain the common lower bound.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/NesbittRatioInequality.lean#L98-L127
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/NesbittRatioInequality.lean#L98-L127

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality
set_option autoImplicit false
open FrontierMathLean

theorem FrontierMathLean.normalized_nesbitt_ratio_eq_iff
    {x y r : ℝ} (hr : 1 < r) (hrx : r ≤ x) (hry : r ≤ y) :
    1 / (x + y) + x / (1 + y) + y / (1 + x) =
        (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) ↔
      x = r ∧ y = r := by sorry
