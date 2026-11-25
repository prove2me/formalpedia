-- Prove2me | Theorems.Thm_NashWilliams_cutF_split
-- name    : NashWilliams.cutF_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:55:10.710814+00:00
-- url     : https://prove2.me/theorems/064b5de9-4d3e-432f-9dfb-5f866c2780a3
-- title:
--   Nash Williams: cut F split
-- statement:
--   The Nash Williams construction uses the cut F split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L80-L88
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L80-L88

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_split [DecidableEq ι] {ends : ι → V × V} {F : Finset ι} {i j : ι} (hi : i ∈ F)
    (hj : j ∈ F) (hij : i ≠ j) (u v : V) (S : Finset V) :
    cutF ends F S + cr (u, v) S =
      cutF (Function.update ends i (u, v)) (F.erase j) S + cr (ends i) S + cr (ends j) S := by sorry
