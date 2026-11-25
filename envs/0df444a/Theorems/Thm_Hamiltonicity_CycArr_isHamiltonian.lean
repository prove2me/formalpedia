-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_isHamiltonian
-- name    : Hamiltonicity.CycArr.isHamiltonian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:24.857502+00:00
-- url     : https://prove2.me/theorems/b571b155-b73b-470e-91dc-e2558adc2fa7
-- title:
--   Cyc Arr: is Hamiltonian
-- statement:
--   A cyclic arrangement through all vertices gives a Hamiltonian graph.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L169-L173
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L169-L173

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}

theorem Hamiltonicity.CycArr.isHamiltonian [Fintype V] [DecidableEq V] (h : CycArr G m f)
    (hm : m = Fintype.card V) : G.IsHamiltonian := by sorry
