-- Prove2me | Theorems.Thm_Hamiltonicity_exists_cycArr_of_isHamiltonian
-- name    : Hamiltonicity.exists_cycArr_of_isHamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:30.244878+00:00
-- url     : https://prove2.me/theorems/b4d71162-9328-5702-b354-72c17f391732
-- title:
--   Hamiltonicity: exists cyc Arr of is Hamiltonian
-- statement:
--   A Hamiltonian graph on at least three vertices has a cyclic arrangement through all
--   vertices.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L198-L204
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L198-L204

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.exists_cycArr_of_isHamiltonian [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsHamiltonian) (hn : 3 ≤ Fintype.card V) :
    ∃ f, CycArr G (Fintype.card V) f := by sorry
