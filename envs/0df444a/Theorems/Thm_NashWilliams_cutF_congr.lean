-- Prove2me | Theorems.Thm_NashWilliams_cutF_congr
-- name    : NashWilliams.cutF_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:46.176487+00:00
-- url     : https://prove2.me/theorems/3e8ce2b9-b467-5d7a-a047-fd4de1ab9a92
-- title:
--   Nash Williams: cut F congr
-- statement:
--   The Nash Williams construction uses the cut F congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L70-L75
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L70-L75

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_congr {ends : ι → V × V} {F : Finset ι} {S S' : Finset V}
    (h : ∀ i ∈ F, (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S) ↔
      ((ends i).1 ∈ S') ≠ ((ends i).2 ∈ S'))) :
    cutF ends F S = cutF ends F S' := by sorry
