-- Prove2me | Theorems.Thm_NashWilliams_cutF_erase_le
-- name    : NashWilliams.cutF_erase_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:21:35.268388+00:00
-- url     : https://prove2.me/theorems/e189cfff-4a24-4c8d-99ae-667814942cfc
-- title:
--   Nash Williams: cut F erase le
-- statement:
--   The Nash Williams construction uses the cut F erase le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L102-L105
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L102-L105

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_erase_le (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι] (i : ι) :
    cutF ends (F.erase i) S ≤ cutF ends F S := by sorry
