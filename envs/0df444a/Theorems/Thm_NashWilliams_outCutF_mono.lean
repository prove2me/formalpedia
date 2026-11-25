-- Prove2me | Theorems.Thm_NashWilliams_outCutF_mono
-- name    : NashWilliams.outCutF_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:10:45.990384+00:00
-- url     : https://prove2.me/theorems/312f5644-014e-424b-a16c-af1afbae3f91
-- title:
--   Nash Williams: out Cut F mono
-- statement:
--   The Nash Williams construction uses the out Cut F mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L42-L45
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L42-L45

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

theorem NashWilliams.outCutF_mono {ends : ι → V × V} {o : ι → Bool} {F G : Finset ι} (h : F ⊆ G)
    (S : Finset V) : outCutF ends o F S ≤ outCutF ends o G S := by sorry
