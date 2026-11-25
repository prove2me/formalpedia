-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_eq_iff
-- name    : Hamiltonicity.CycArr.eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:12:26.715004+00:00
-- url     : https://prove2.me/theorems/a9faa047-6ad5-4a3e-88f9-136e51e12d0b
-- title:
--   Cyc Arr: eq iff
-- statement:
--   The Cyc Arr construction uses the eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L47-L53
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L47-L53

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

theorem Hamiltonicity.CycArr.eq_iff (h : CycArr G m f) {i j : ℕ} : f i = f j ↔ i % m = j % m := by sorry
