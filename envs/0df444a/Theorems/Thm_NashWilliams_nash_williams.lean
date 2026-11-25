-- Prove2me | Theorems.Thm_NashWilliams_nash_williams
-- name    : NashWilliams.nash_williams
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:05:56.773+00:00
-- url     : https://prove2.me/theorems/49da36e5-086c-4db7-8d65-e2546d8735e2
-- title:
--   Nash Williams: nash williams
-- statement:
--   **Nash-Williams' weak orientation theorem (1960).** Every `2k`-edge-connected finite loopless
--   multigraph has a `k`-arc-connected orientation. (The looplessness hypothesis `_hloop` is part of
--   the requested statement; the proof does not need it, since loops never cross a cut, hence the
--   underscore in its name.)
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L62-L74
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L62-L74

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

theorem NashWilliams.nash_williams (k : ℕ) (ends : ι → V × V) (_hloop : ∀ i, (ends i).1 ≠ (ends i).2)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 * k ≤ cut ends S) :
    ∃ o : ι → Bool, ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ outCut ends o S := by sorry
