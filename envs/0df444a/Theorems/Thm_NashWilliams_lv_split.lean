-- Prove2me | Theorems.Thm_NashWilliams_lv_split
-- name    : NashWilliams.lv_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:11:20.115968+00:00
-- url     : https://prove2.me/theorems/4ccc5b98-6287-4d20-abda-dd92e2bc8055
-- title:
--   Nash Williams: lv split
-- statement:
--   The Nash Williams construction uses the lv split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L65-L70
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L65-L70

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]

theorem NashWilliams.lv_split {s u v : V} {p q : V × V} (hp : Joins s u p) (hq : Joins s v q) (b : Bool)
    (S : Finset V) :
    lv (u, v) b S ≤ lv p (if p.2 = s then b else !b) S + lv q (if q.1 = s then b else !b) S := by sorry
