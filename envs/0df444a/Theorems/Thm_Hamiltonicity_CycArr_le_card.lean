-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_le_card
-- name    : Hamiltonicity.CycArr.le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:52.940779+00:00
-- url     : https://prove2.me/theorems/6d5f00f1-766a-455e-b958-6ce943ff3de6
-- title:
--   Cyc Arr: le card
-- statement:
--   In a cyclic arrangement `m ≤ |V|`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L176-L183
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L176-L183

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

theorem Hamiltonicity.CycArr.le_card [Fintype V] (h : CycArr G m f) : m ≤ Fintype.card V := by sorry
