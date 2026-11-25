-- Prove2me | Theorems.Thm_NashWilliams_outCut_eq_outCutF
-- name    : NashWilliams.outCut_eq_outCutF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:15:40.838814+00:00
-- url     : https://prove2.me/theorems/f325d2da-2439-5655-869b-41b9fe491da7
-- title:
--   Nash Williams: out Cut eq out Cut F
-- statement:
--   The Nash Williams construction uses the out Cut eq out Cut F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L50-L56
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L50-L56

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
omit [Fintype V]

theorem NashWilliams.outCut_eq_outCutF (ends : ι → V × V) (o : ι → Bool) (S : Finset V) :
    outCut ends o S = outCutF ends o Finset.univ S := by sorry
