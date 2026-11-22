-- Prove2me | Theorems.Thm_GridHam_mem_rightDetour
-- name    : GridHam.mem_rightDetour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:58:07.980091+00:00
-- url     : https://prove2.me/theorems/e5bd2c8e-cb0e-4d25-af7b-61233570c3b2
-- title:
--   Grid Ham: mem right Detour
-- statement:
--   The Grid Ham construction uses the mem right Detour property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L775-L783
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L775-L783

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.mem_rightDetour (w h y : ℕ) (hy : y + 1 < h) (u : Coord) :
    u ∈ rightDetour w h y ↔ (u.1 = w ∧ u.2 < h) ∨ (u.1 = w + 1 ∧ u.2 < h) := by sorry
