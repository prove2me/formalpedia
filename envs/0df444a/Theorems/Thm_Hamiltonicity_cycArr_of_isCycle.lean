-- Prove2me | Theorems.Thm_Hamiltonicity_cycArr_of_isCycle
-- name    : Hamiltonicity.cycArr_of_isCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:38.272925+00:00
-- url     : https://prove2.me/theorems/3fbb2466-9c3e-40bb-b0b7-469f567e94ff
-- title:
--   Hamiltonicity: cyc Arr of is Cycle
-- statement:
--   A cycle gives a cyclic arrangement of the same length.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L188-L194
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L188-L194

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.cycArr_of_isCycle {G : SimpleGraph V} {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    CycArr G c.length (fun i => c.getVert (i % c.length)) := by sorry
