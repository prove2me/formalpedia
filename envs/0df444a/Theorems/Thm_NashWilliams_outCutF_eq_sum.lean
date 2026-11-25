-- Prove2me | Theorems.Thm_NashWilliams_outCutF_eq_sum
-- name    : NashWilliams.outCutF_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:10:33.923724+00:00
-- url     : https://prove2.me/theorems/53650b2c-7f16-453e-a620-4a6ca6ec0d8d
-- title:
--   Nash Williams: out Cut F eq sum
-- statement:
--   The Nash Williams construction uses the out Cut F eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L36-L39
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L36-L39

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

theorem NashWilliams.outCutF_eq_sum (ends : ι → V × V) (o : ι → Bool) (F : Finset ι) (S : Finset V) :
    outCutF ends o F S = ∑ i ∈ F, lv (ends i) (o i) S := by sorry
