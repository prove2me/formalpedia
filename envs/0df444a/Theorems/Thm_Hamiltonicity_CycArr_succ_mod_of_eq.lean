-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_succ_mod_of_eq
-- name    : Hamiltonicity.CycArr.succ_mod_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:12:09.659106+00:00
-- url     : https://prove2.me/theorems/4c08e020-42e4-5c13-a5cb-c7849b16f9cd
-- title:
--   Cyc Arr: succ mod of eq
-- statement:
--   The Cyc Arr construction uses the succ mod of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L74-L77
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L74-L77

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

theorem Hamiltonicity.CycArr.succ_mod_of_eq {i : ℕ} (hc : i % m + 1 = m) : (i + 1) % m = 0 := by sorry
