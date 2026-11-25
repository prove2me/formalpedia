-- Prove2me | Theorems.Thm_Hamiltonicity_CycArr_pos
-- name    : Hamiltonicity.CycArr.pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:12:42.453097+00:00
-- url     : https://prove2.me/theorems/ff5c497a-5895-4e34-8d5b-4e7379c6330e
-- title:
--   Cyc Arr: pos
-- statement:
--   The Cyc Arr construction uses the pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L39-L39
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/CyclicArrangement.lean#L39-L39

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

theorem Hamiltonicity.CycArr.pos (h : CycArr G m f) : 0 < m := by sorry
