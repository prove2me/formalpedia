-- Prove2me | Theorems.Thm_NashWilliams_cr_singleton_of_joins
-- name    : NashWilliams.cr_singleton_of_joins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:00:16.750532+00:00
-- url     : https://prove2.me/theorems/5a5ac982-49d7-445b-8a77-f4c8d2d6c2cf
-- title:
--   Nash Williams: cr singleton of joins
-- statement:
--   The Nash Williams construction uses the cr singleton of joins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L94-L95
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L94-L95

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cr_singleton_of_joins {s u : V} {p : V × V} (hJ : Joins s u p) : cr p {s} = 1 := by sorry
