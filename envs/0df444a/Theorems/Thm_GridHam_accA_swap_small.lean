-- Prove2me | Theorems.Thm_GridHam_accA_swap_small
-- name    : GridHam.accA_swap_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:01:35.204944+00:00
-- url     : https://prove2.me/theorems/5a674d70-858f-46b1-be67-95ecd96a0d6e
-- title:
--   Grid Ham: acc A swap small
-- statement:
--   The Grid Ham construction uses the acc A swap small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L187-L190
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L187-L190

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxRecDepth 100000

theorem GridHam.accA_swap_small : ∀ w ∈ List.range 4, ∀ h ∈ List.range 4, ∀ sx ∈ List.range w,
    ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    (AccA w h sx sy tx ty ↔ AccA w h tx ty sx sy) := by sorry
