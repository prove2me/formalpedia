-- Prove2me | Theorems.Thm_GridHam_rightDetour_length
-- name    : GridHam.rightDetour_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:58:17.902491+00:00
-- url     : https://prove2.me/theorems/94561303-0d2d-4b18-98c5-d6f984237e6d
-- title:
--   Grid Ham: right Detour length
-- statement:
--   The Grid Ham construction uses the right Detour length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L785-L789
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L785-L789

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.rightDetour_length (w h y : ℕ) (hy : y + 1 < h) :
    (rightDetour w h y).length = 2 * h := by sorry
