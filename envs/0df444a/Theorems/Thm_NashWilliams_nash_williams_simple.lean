-- Prove2me | Theorems.Thm_NashWilliams_nash_williams_simple
-- name    : NashWilliams.nash_williams_simple
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:06:23.211967+00:00
-- url     : https://prove2.me/theorems/0c67b219-984e-53d5-a43f-867c9fe88512
-- title:
--   Nash Williams: nash williams simple
-- statement:
--   **Nash-Williams' weak orientation theorem for simple graphs.** Every finite
--   `2k`-edge-connected simple graph has an orientation in which every nonempty proper vertex set has
--   at least `k` leaving arcs. (The hypothesis `[Nonempty V]` is part of the requested statement; the
--   proof does not need it.) The filter in the conclusion is over a predicate on an arbitrary digraph
--   `D`, so its decidability is provided classically (`open Classical in`).
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L226-L235
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Defs.lean#L226-L235

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
open Classical

theorem NashWilliams.nash_williams_simple {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (k : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected (2 * k)) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        k ≤ ((S ×ˢ Sᶜ).filter fun q => D.Adj q.1 q.2).card := by sorry
