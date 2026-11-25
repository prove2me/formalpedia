-- Prove2me | Theorems.Thm_NashWilliams_cutF_le_erase_add_one
-- name    : NashWilliams.cutF_le_erase_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:50:19.385471+00:00
-- url     : https://prove2.me/theorems/0fb51304-77a2-4940-bbb6-fd4d3ebfeca5
-- title:
--   Nash Williams: cut F le erase add one
-- statement:
--   The Nash Williams construction uses the cut F le erase add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L107-L114
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L107-L114

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_le_erase_add_one (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι]
    (i : ι) : cutF ends F S ≤ cutF ends (F.erase i) S + 1 := by sorry
