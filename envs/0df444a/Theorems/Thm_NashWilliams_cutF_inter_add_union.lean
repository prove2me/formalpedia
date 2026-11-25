-- Prove2me | Theorems.Thm_NashWilliams_cutF_inter_add_union
-- name    : NashWilliams.cutF_inter_add_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:50:10.107977+00:00
-- url     : https://prove2.me/theorems/b81dc650-e086-4dea-83c9-591688a4c85f
-- title:
--   Nash Williams: cut F inter add union
-- statement:
--   Submodularity of the cut function.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L78-L84
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L78-L84

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_inter_add_union (ends : ι → V × V) (F : Finset ι) (X Y : Finset V) :
    cutF ends F (X ∩ Y) + cutF ends F (X ∪ Y) ≤ cutF ends F X + cutF ends F Y := by sorry
