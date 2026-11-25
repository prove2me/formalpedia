-- Prove2me | Theorems.Thm_NashWilliamsOrientation_nash_williams
-- name    : NashWilliamsOrientation.nash_williams
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:48:19.243114+00:00
-- url     : https://prove2.me/theorems/014351f9-16a9-52b3-a5d7-dab57975c943
-- title:
--   Nash Williams Orientation: nash williams
-- statement:
--   **Nash-Williams' weak orientation theorem.** A finite loopless multigraph, given by an edge
--   family `ends : ι → V × V`, in which every nonempty proper vertex set is left by at least `2k`
--   edges has an orientation `o : ι → Bool` in which every such set is left by at least `k` arcs.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/Solution.lean#L40-L43
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/Solution.lean#L40-L43

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Defs
public import Definitions.Def_NashWilliamsOrientation_Solution
public import Theorems.Thm_NashWilliams_nash_williams

set_option autoImplicit true
@[expose] public section
public section
open NashWilliamsOrientation
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]

theorem NashWilliamsOrientation.nash_williams (k : ℕ) (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 * k ≤ cut ends S) :
    ∃ o : ι → Bool, ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ outCut ends o S := by sorry
