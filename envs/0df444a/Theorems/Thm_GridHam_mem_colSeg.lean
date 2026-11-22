-- Prove2me | Theorems.Thm_GridHam_mem_colSeg
-- name    : GridHam.mem_colSeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:38:05.501954+00:00
-- url     : https://prove2.me/theorems/2ac0aa14-5651-4b5a-a649-69992b8e29e0
-- title:
--   Grid Ham: mem col Seg
-- statement:
--   The Grid Ham construction uses the mem col Seg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L506-L541
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L506-L541

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.mem_colSeg (c lo : ℕ) : ∀ k (v : Coord),
    v ∈ colSeg c lo k ↔ v.1 = c ∧ lo ≤ v.2 ∧ v.2 ≤ lo + k := by sorry
