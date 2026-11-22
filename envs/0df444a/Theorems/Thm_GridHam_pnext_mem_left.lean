-- Prove2me | Theorems.Thm_GridHam_pnext_mem_left
-- name    : GridHam.pnext_mem_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:32:43.734027+00:00
-- url     : https://prove2.me/theorems/45a68de1-b6b9-45fa-9da5-44da5f7977d2
-- title:
--   Grid Ham: pnext mem left
-- statement:
--   The Grid Ham construction uses the pnext mem left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L36-L39
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L36-L39

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.pnext_mem_left {p : List Coord} {x y : Coord} (h : PNext p x y) : x ∈ p := by sorry
