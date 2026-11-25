-- Prove2me | Theorems.Thm_NashWilliams_exists_tight_of_not_req
-- name    : NashWilliams.exists_tight_of_not_req
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:55:31.202691+00:00
-- url     : https://prove2.me/theorems/fd8ee584-b1d8-4d29-9f58-64957cd5cdfa
-- title:
--   Nash Williams: exists tight of not req
-- statement:
--   The Nash Williams construction uses the exists tight of not req property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Mader.lean#L32-L42
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Mader.lean#L32-L42

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Mader
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem NashWilliams.exists_tight_of_not_req {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) {i : ι} (hi : ¬ Req K T ends (F.erase i)) :
    ∃ S, Tight K T ends F S ∧ (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S)) := by sorry
