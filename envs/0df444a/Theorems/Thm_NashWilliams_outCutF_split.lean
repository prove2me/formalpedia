-- Prove2me | Theorems.Thm_NashWilliams_outCutF_split
-- name    : NashWilliams.outCutF_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:11:20.033421+00:00
-- url     : https://prove2.me/theorems/236af87e-2d9c-557f-9cfd-e547664971c0
-- title:
--   Nash Williams: out Cut F split
-- statement:
--   The Nash Williams construction uses the out Cut F split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L80-L89
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L80-L89

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

theorem NashWilliams.outCutF_split {ends : ι → V × V} {F : Finset ι} {i j : ι} (hi : i ∈ F) (hj : j ∈ F)
    (hij : i ≠ j) {s u v : V} (o1 : ι → Bool) (S : Finset V) :
    outCutF ends (liftO s ends o1 i j) F S + lv (u, v) (o1 i) S =
      outCutF (Function.update ends i (u, v)) o1 (F.erase j) S +
        lv (ends i) (liftO s ends o1 i j i) S + lv (ends j) (liftO s ends o1 i j j) S := by sorry
