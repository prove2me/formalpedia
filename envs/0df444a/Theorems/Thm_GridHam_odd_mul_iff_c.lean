-- Prove2me | Theorems.Thm_GridHam_odd_mul_iff_c
-- name    : GridHam.odd_mul_iff_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:23:59.156795+00:00
-- url     : https://prove2.me/theorems/46c92ab5-f51d-48ad-b7e4-cb0ffd4fd176
-- title:
--   Grid Ham: odd mul iff c
-- statement:
--   The Grid Ham construction uses the odd mul iff c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L175-L179
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean#L175-L179

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.odd_mul_iff_c (w h : ℕ) : (w * h) % 2 = 1 ↔ w % 2 = 1 ∧ h % 2 = 1 := by sorry
