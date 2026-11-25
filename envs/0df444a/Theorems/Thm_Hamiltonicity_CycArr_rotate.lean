-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_rotate
-- name    : Hamiltonicity.CycArr.rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:14:19.855076+00:00
-- url     : https://prove2.me/theorems/97034012-15dc-4b7f-a54d-60b74c5b6943
-- title:
--   Cyc Arr: rotate
-- statement:
--   The Cyc Arr construction uses the rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L59-L67
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L59-L67

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

theorem Hamiltonicity.CycArr.rotate (h : CycArr G m f) (a : ℕ) : CycArr G m (fun i => f (a + i)) := by sorry
