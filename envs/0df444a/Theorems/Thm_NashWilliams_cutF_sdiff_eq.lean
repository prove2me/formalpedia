-- Prove2me | Theorems.Thm_NashWilliams_cutF_sdiff_eq
-- name    : NashWilliams.cutF_sdiff_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T17:50:18.104121+00:00
-- url     : https://prove2.me/theorems/a09da288-024b-4d6e-8556-d2ef9c41e6e3
-- title:
--   Nash Williams: cut F sdiff eq
-- statement:
--   Complementation inside `T` does not change the cut.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L96-L100
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L96-L100

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_sdiff_eq {T : Finset V} {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F)
    (S : Finset V) : cutF ends F (T \ S) = cutF ends F S := by sorry
