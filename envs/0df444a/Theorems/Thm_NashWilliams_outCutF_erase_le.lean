-- Prove2me | Theorems.Thm_NashWilliams_outCutF_erase_le
-- name    : NashWilliams.outCutF_erase_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:11.693978+00:00
-- url     : https://prove2.me/theorems/cedf4e67-2125-4cce-ad24-f596366cfa5e
-- title:
--   Nash Williams: out Cut F erase le
-- statement:
--   The Nash Williams construction uses the out Cut F erase le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L124-L127
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L124-L127

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.outCutF_erase_le (ends : ι → V × V) (o : ι → Bool) (F : Finset ι) (S : Finset V)
    [DecidableEq ι] (i : ι) : outCutF ends o (F.erase i) S ≤ outCutF ends o F S := by sorry
