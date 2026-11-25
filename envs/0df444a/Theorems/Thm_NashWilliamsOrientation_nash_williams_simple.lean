-- Prove2me | Theorems.Thm_NashWilliamsOrientation_nash_williams_simple
-- name    : NashWilliamsOrientation.nash_williams_simple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:50:43.272439+00:00
-- url     : https://prove2.me/theorems/565a33fe-7240-5142-9d93-15d73b3d09f8
-- title:
--   Nash Williams Orientation: nash williams simple
-- statement:
--   **Nash-Williams' theorem for simple graphs.** Every finite `2k`-edge-connected simple graph
--   has an orientation (a `Digraph` with underlying graph `G` and no pair of opposite arcs) in which
--   every nonempty proper vertex set has at least `k` leaving arcs.
--
--   Source: https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/Solution.lean#L51-L56
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/Solution.lean#L51-L56

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Defs
public import Definitions.Def_NashWilliamsOrientation_Solution
public import Theorems.Thm_NashWilliams_nash_williams_simple

set_option autoImplicit true
@[expose] public section
public section
open NashWilliamsOrientation
open Classical

theorem NashWilliamsOrientation.nash_williams_simple {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (k : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected (2 * k)) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        k ≤ ((S ×ˢ Sᶜ).filter fun q => D.Adj q.1 q.2).card := by sorry
