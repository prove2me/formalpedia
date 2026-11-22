-- Prove2me | Theorems.Thm_GridHam_colorCompatible_iff
-- name    : GridHam.colorCompatible_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:52:46.482565+00:00
-- url     : https://prove2.me/theorems/f7da6734-d160-49ce-9fc5-5b5b6e0705cc
-- title:
--   Grid Ham: color Compatible iff
-- statement:
--   The Grid Ham construction uses the color Compatible iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L63-L74
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L63-L74

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.colorCompatible_iff (w h sx sy tx ty : ℕ) :
    ColorCompatible w h (sx, sy) (tx, ty) ↔
      ((w % 2 = 1 ∧ h % 2 = 1 ∧ (sx + sy) % 2 = 0 ∧ (tx + ty) % 2 = 0) ∨
        (¬ (w % 2 = 1 ∧ h % 2 = 1) ∧ (sx + sy) % 2 ≠ (tx + ty) % 2)) := by sorry
