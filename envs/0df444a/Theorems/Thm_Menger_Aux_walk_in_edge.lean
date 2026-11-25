-- Prove2me | Theorems.Thm_Menger_Aux_walk_in_edge
-- name    : Menger.Aux.walk_in_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:56.048225+00:00
-- url     : https://prove2.me/theorems/a2b23aa2-6339-4508-9c13-1e4f99f5da57
-- title:
--   Aux: walk in edge
-- statement:
--   The Aux construction uses the walk in edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L445-L452
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L445-L452

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.walk_in_edge {G : SimpleGraph V} (e : G.edgeSet) {z m : V} (hz : z ∈ (e : Sym2 V))
    (hm : m ∈ (e : Sym2 V)) : ∃ r : G.Walk z m, ∀ f ∈ r.edges, f = (e : Sym2 V) := by sorry
