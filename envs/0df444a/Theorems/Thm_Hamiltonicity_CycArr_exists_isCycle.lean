-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_exists_isCycle
-- name    : Hamiltonicity.CycArr.exists_isCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:17.897955+00:00
-- url     : https://prove2.me/theorems/59fb9b03-1240-57c8-be89-2c9db67ec4db
-- title:
--   Cyc Arr: exists is Cycle
-- statement:
--   A cyclic arrangement gives a cycle of the same length.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L136-L166
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L136-L166

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

theorem Hamiltonicity.CycArr.exists_isCycle (h : CycArr G m f) :
    ∃ c : G.Walk (f 0) (f 0), c.IsCycle ∧ c.length = m := by sorry
