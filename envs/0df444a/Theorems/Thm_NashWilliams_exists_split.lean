-- Prove2me | Theorems.Thm_NashWilliams_exists_split
-- name    : NashWilliams.exists_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:08:54.578747+00:00
-- url     : https://prove2.me/theorems/011dddea-7ad3-5813-9661-6ae5ce887537
-- title:
--   Nash Williams: exists split
-- statement:
--   **Lovász's splitting lemma.**
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L180-L336
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Splitting.lean#L180-L336

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]

theorem NashWilliams.exists_split [DecidableEq ι] {K : ℕ} (hK : 2 ≤ K) {T : Finset V} {s : V}
    {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F) (hreq : Req K (T.erase s) ends F)
    (heven : Even (cutF ends F {s})) (hpos : 0 < cutF ends F {s}) :
    ∃ i ∈ F, ∃ j ∈ F, ∃ u v : V, i ≠ j ∧ Joins s u (ends i) ∧ Joins s v (ends j) ∧
      Req K (T.erase s) (Function.update ends i (u, v)) (F.erase j) := by sorry
