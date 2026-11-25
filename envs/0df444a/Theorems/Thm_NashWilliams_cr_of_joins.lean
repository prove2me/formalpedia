-- Prove2me | Theorems.Thm_NashWilliams_cr_of_joins
-- name    : NashWilliams.cr_of_joins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:59:58.835659+00:00
-- url     : https://prove2.me/theorems/22bbc463-9583-5625-9aac-b0c08d73e408
-- title:
--   Nash Williams: cr of joins
-- statement:
--   The Nash Williams construction uses the cr of joins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L90-L92
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L90-L92

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cr_of_joins {s u : V} {p : V × V} (hJ : Joins s u p) {S : Finset V} (hs : s ∉ S) :
    cr p S = if u ∈ S then 1 else 0 := by sorry
