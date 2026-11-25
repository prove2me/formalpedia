-- Prove2me | Theorems.Thm_NashWilliams_cutF_eq_sum
-- name    : NashWilliams.cutF_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:56.294913+00:00
-- url     : https://prove2.me/theorems/3cac69b5-439d-4ed3-af51-e03232cf4ea3
-- title:
--   Nash Williams: cut F eq sum
-- statement:
--   The Nash Williams construction uses the cut F eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L59-L61
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean#L59-L61

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.cutF_eq_sum (ends : ι → V × V) (F : Finset ι) (S : Finset V) :
    cutF ends F S = ∑ i ∈ F, cr (ends i) S := by sorry
