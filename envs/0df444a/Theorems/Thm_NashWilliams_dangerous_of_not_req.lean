-- Prove2me | Theorems.Thm_NashWilliams_dangerous_of_not_req
-- name    : NashWilliams.dangerous_of_not_req
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:00:33.15952+00:00
-- url     : https://prove2.me/theorems/f353bf20-b97b-4c70-aa50-2a036af20106
-- title:
--   Nash Williams: dangerous of not req
-- statement:
--   If splitting off `su`, `sv` violates the requirement, then `u` and `v` lie in a dangerous
--   set.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L99-L115
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L99-L115

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.dangerous_of_not_req [DecidableEq ι] {K : ℕ} {T : Finset V} {s : V} {ends : ι → V × V}
    {F : Finset ι} (hreq : Req K (T.erase s) ends F) {i j : ι} (hi : i ∈ F) (hj : j ∈ F)
    (hij : i ≠ j) {u v : V} (hJi : Joins s u (ends i)) (hJj : Joins s v (ends j))
    (hfail : ¬ Req K (T.erase s) (Function.update ends i (u, v)) (F.erase j)) :
    ∃ X ⊆ T.erase s, X ≠ T.erase s ∧ u ∈ X ∧ v ∈ X ∧ cutF ends F X ≤ K + 1 := by sorry
