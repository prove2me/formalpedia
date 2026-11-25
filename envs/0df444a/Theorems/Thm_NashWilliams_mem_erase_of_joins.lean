-- Prove2me | Theorems.Thm_NashWilliams_mem_erase_of_joins
-- name    : NashWilliams.mem_erase_of_joins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:11:25.242443+00:00
-- url     : https://prove2.me/theorems/40b8ba5a-1517-5501-8873-5cb9dd70ba4f
-- title:
--   Nash Williams: mem erase of joins
-- statement:
--   The Nash Williams construction uses the mem erase of joins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L92-L97
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L92-L97

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

theorem NashWilliams.mem_erase_of_joins {T : Finset V} {s u : V} {ends : ι → V × V} {F : Finset ι}
    (hin : Inside T ends F) {i : ι} (hi : i ∈ F) (hJ : Joins s u (ends i)) : u ∈ T.erase s := by sorry
