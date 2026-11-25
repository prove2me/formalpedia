-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_eq_mod
-- name    : Hamiltonicity.CycArr.eq_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:12:47.753255+00:00
-- url     : https://prove2.me/theorems/c41efec8-14f2-4eda-8403-4f1634f5a966
-- title:
--   Cyc Arr: eq mod
-- statement:
--   The Cyc Arr construction uses the eq mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L41-L45
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L41-L45

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

theorem Hamiltonicity.CycArr.eq_mod (h : CycArr G m f) (i : ℕ) : f i = f (i % m) := by sorry
