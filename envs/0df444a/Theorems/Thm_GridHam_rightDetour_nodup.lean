-- Prove2me | Theorems.Thm_GridHam_rightDetour_nodup
-- name    : GridHam.rightDetour_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:58:17.293802+00:00
-- url     : https://prove2.me/theorems/5a4d0d5c-e8b5-4ecf-8d70-25331d705da5
-- title:
--   Grid Ham: right Detour nodup
-- statement:
--   The Grid Ham construction uses the right Detour nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L791-L805
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L791-L805

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.rightDetour_nodup (w h y : ℕ) (_hy : y + 1 < h) : (rightDetour w h y).Nodup := by sorry
