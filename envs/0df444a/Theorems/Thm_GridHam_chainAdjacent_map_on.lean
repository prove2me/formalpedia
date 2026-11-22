-- Prove2me | Theorems.Thm_GridHam_chainAdjacent_map_on
-- name    : GridHam.chainAdjacent_map_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:48.906482+00:00
-- url     : https://prove2.me/theorems/713c063f-95f1-409d-ba3c-eff8b85bb0ae
-- title:
--   Grid Ham: chain Adjacent map on
-- statement:
--   The Grid Ham construction uses the chain Adjacent map on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1029-L1056
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1029-L1056

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.chainAdjacent_map_on (f : Coord → Coord) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ u ∈ l, Adjacent v u → Adjacent (f v) (f u)) →
    chainAdjacent l = true → chainAdjacent (l.map f) = true := by sorry
