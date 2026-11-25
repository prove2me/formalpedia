-- Prove2me | Theorems.Thm_NashWilliams_cutF_erase_eq
-- name    : NashWilliams.cutF_erase_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:50:15.131869+00:00
-- url     : https://prove2.me/theorems/2126ea22-e4f1-5f19-bc04-7ed58616c360
-- title:
--   Nash Williams: cut F erase eq
-- statement:
--   The Nash Williams construction uses the cut F erase eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L116-L122
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L116-L122

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_erase_eq (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι] (i : ι)
    (h : ¬ (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S))) :
    cutF ends (F.erase i) S = cutF ends F S := by sorry
