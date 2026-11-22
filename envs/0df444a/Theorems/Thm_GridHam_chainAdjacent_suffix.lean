-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_suffix
-- name    : GridHam.chainAdjacent_suffix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:28:50.861401+00:00
-- url     : https://prove2.me/theorems/4172fd57-0a4f-49cc-8550-07121e232155
-- title:
--   Grid Ham: chain Adjacent suffix
-- statement:
--   The Grid Ham construction uses the chain Adjacent suffix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L654-L659
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L654-L659

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_suffix : ∀ (l1 m : List Coord),
    chainAdjacent (l1 ++ m) = true → chainAdjacent m = true := by sorry
