-- Prove2me | Theorems.Thm_Menger_Aux_lower_from_lineGraph
-- name    : Menger.Aux.lower_from_lineGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:09:24.827525+00:00
-- url     : https://prove2.me/theorems/64cc98e0-19b8-5bb8-b97e-4c8d42431570
-- title:
--   Aux: lower from line Graph
-- statement:
--   A walk in the line graph gives a walk of `G` using only edges in its support.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L455-L470
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L455-L470

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.lower_from_lineGraph {G : SimpleGraph V} :
    ∀ {e f : G.edgeSet} (q : G.lineGraph.Walk e f) {z z' : V}, z ∈ (e : Sym2 V) →
      z' ∈ (f : Sym2 V) → ∃ r : G.Walk z z', ∀ g ∈ r.edges, ∃ e'' ∈ q.support, g = (e'' : Sym2 V)
  := by sorry
