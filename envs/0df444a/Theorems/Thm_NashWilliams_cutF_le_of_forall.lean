-- Prove2me | Theorems.Thm_NashWilliams_cutF_le_of_forall
-- name    : NashWilliams.cutF_le_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:39:57.493339+00:00
-- url     : https://prove2.me/theorems/ca3ba503-be32-47ef-9f37-54769ceff719
-- title:
--   Nash Williams: cut F le of forall
-- statement:
--   The Nash Williams construction uses the cut F le of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L63-L68
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L63-L68

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_le_of_forall {ends : ι → V × V} {F : Finset ι} {S S' : Finset V}
    (h : ∀ i ∈ F, ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S) → ((ends i).1 ∈ S') ≠ ((ends i).2 ∈ S')) :
    cutF ends F S ≤ cutF ends F S' := by sorry
