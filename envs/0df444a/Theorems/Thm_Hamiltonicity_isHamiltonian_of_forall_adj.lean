-- Prove2me | Theorems.Thm_Hamiltonicity_isHamiltonian_of_forall_adj
-- name    : Hamiltonicity.isHamiltonian_of_forall_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:13.499008+00:00
-- url     : https://prove2.me/theorems/ea0baf49-c400-429d-af19-c15300bff236
-- title:
--   Hamiltonicity: is Hamiltonian of forall adj
-- statement:
--   A graph in which any two distinct vertices are adjacent is Hamiltonian (if it has at least
--   three vertices).
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L208-L233
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L208-L233

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.isHamiltonian_of_forall_adj [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hn : 3 ≤ Fintype.card V) (hadj : ∀ u v, u ≠ v → G.Adj u v) : G.IsHamiltonian := by sorry
