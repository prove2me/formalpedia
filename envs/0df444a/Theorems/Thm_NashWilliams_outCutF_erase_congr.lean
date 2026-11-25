-- Prove2me | Theorems.Thm_NashWilliams_outCutF_erase_congr
-- name    : NashWilliams.outCutF_erase_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:11:03.055884+00:00
-- url     : https://prove2.me/theorems/1d0bfe9a-6d2b-406a-a22f-177c6ef78509
-- title:
--   Nash Williams: out Cut F erase congr
-- statement:
--   The Nash Williams construction uses the out Cut F erase congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L48-L56
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L48-L56

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

theorem NashWilliams.outCutF_erase_congr {ends : ι → V × V} {o : ι → Bool} {F : Finset ι} {s : V}
    (h : ∀ l ∈ F, (ends l).1 ≠ s ∧ (ends l).2 ≠ s) (S : Finset V) :
    outCutF ends o F (S.erase s) = outCutF ends o F S := by sorry
