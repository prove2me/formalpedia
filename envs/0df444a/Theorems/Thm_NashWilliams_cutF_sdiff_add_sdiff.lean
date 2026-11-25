-- Prove2me | Theorems.Thm_NashWilliams_cutF_sdiff_add_sdiff
-- name    : NashWilliams.cutF_sdiff_add_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:50:13.793288+00:00
-- url     : https://prove2.me/theorems/8e748719-23e8-43fe-9fee-15bda9c6740b
-- title:
--   Nash Williams: cut F sdiff add sdiff
-- statement:
--   Posimodularity of the cut function.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L87-L93
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L87-L93

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_sdiff_add_sdiff (ends : ι → V × V) (F : Finset ι) (X Y : Finset V) :
    cutF ends F (X \ Y) + cutF ends F (Y \ X) ≤ cutF ends F X + cutF ends F Y := by sorry
