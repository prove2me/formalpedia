-- Prove2me | Theorems.Thm_NashWilliams_lv_split_eq
-- name    : NashWilliams.lv_split_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:10:57.425581+00:00
-- url     : https://prove2.me/theorems/edd66549-73bc-5187-b556-9003d551ba01
-- title:
--   Nash Williams: lv split eq
-- statement:
--   The Nash Williams construction uses the lv split eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L73-L78
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L73-L78

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

theorem NashWilliams.lv_split_eq {s u v : V} {p q : V × V} (hp : Joins s u p) (hq : Joins s v q) (b : Bool)
    {X : Finset V} (h : (s ∈ X ∧ u ∉ X ∧ v ∉ X) ∨ (s ∉ X ∧ u ∈ X ∧ v ∈ X)) :
    lv (u, v) b X + 1 =
      lv p (if p.2 = s then b else !b) X + lv q (if q.1 = s then b else !b) X := by sorry
