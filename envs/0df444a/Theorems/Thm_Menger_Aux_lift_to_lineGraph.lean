-- Prove2me | Theorems.Thm_Menger_Aux_lift_to_lineGraph
-- name    : Menger.Aux.lift_to_lineGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:34.24049+00:00
-- url     : https://prove2.me/theorems/6699cd92-9404-4615-86ed-e12e4eefecf6
-- title:
--   Aux: lift to line Graph
-- statement:
--   A walk of `G` starting at a vertex of an edge `e` gives a walk in the line graph from `e`
--   through the edges of the walk.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L422-L443
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L422-L443

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.lift_to_lineGraph {G : SimpleGraph V} :
    ∀ {w z : V} (p : G.Walk w z) (e : G.edgeSet), w ∈ (e : Sym2 V) →
      ∃ e' : G.edgeSet, z ∈ (e' : Sym2 V) ∧ ∃ q : G.lineGraph.Walk e e',
        ∀ f ∈ q.support, f = e ∨ (f : Sym2 V) ∈ p.edges
  := by sorry
