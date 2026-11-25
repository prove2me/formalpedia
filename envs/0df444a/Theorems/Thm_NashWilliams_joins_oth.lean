-- Prove2me | Theorems.Thm_NashWilliams_joins_oth
-- name    : NashWilliams.joins_oth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:59:36.007569+00:00
-- url     : https://prove2.me/theorems/fb3638ca-f2d5-457e-9bee-a1c4ceee58de
-- title:
--   Nash Williams: joins oth
-- statement:
--   The Nash Williams construction uses the joins oth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L41-L51
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L41-L51

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.joins_oth {s : V} {p : V × V} (h : (p.1 = s) ≠ (p.2 = s)) : Joins s (oth s p) p := by sorry
