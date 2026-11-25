-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_succ_mod_of_lt
-- name    : Hamiltonicity.CycArr.succ_mod_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:12:06.952195+00:00
-- url     : https://prove2.me/theorems/16cdc184-bf42-509f-91ea-27bf84442c87
-- title:
--   Cyc Arr: succ mod of lt
-- statement:
--   The Cyc Arr construction uses the succ mod of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L69-L72
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L69-L72

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

theorem Hamiltonicity.CycArr.succ_mod_of_lt {i : ℕ} (hc : i % m + 1 < m) : (i + 1) % m = i % m + 1 := by sorry
