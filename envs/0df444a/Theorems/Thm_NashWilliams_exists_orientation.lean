-- Prove2me | Theorems.Thm_NashWilliams_exists_orientation
-- name    : NashWilliams.exists_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:16:00.411068+00:00
-- url     : https://prove2.me/theorems/e868cbd1-bd3f-4ef8-afa5-62901bb4744a
-- title:
--   Nash Williams: exists orientation
-- statement:
--   **Nash-Williams' weak orientation theorem**, general form: if every nonempty proper subset of
--   `T` has cut at least `2k` (all active edges inside `T`), then the active edges have an orientation
--   in which every nonempty proper subset of `T` has at least `k` leaving arcs.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L178-L269
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Orientation.lean#L178-L269

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

theorem NashWilliams.exists_orientation (k : ℕ) : ∀ (n : ℕ) (T : Finset V) (ends : ι → V × V) (F : Finset ι),
    F.card = n → Inside T ends F → Req (2 * k) T ends F →
    ∃ o : ι → Bool, ∀ S ⊆ T, S.Nonempty → S ≠ T → k ≤ outCutF ends o F S := by sorry
