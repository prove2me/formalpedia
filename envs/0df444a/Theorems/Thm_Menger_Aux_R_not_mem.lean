-- Prove2me | Theorems.Thm_Menger_Aux_R_not_mem
-- name    : Menger.Aux.R.not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:01.176309+00:00
-- url     : https://prove2.me/theorems/2cd6d543-bc80-4622-8d8a-68f79bda1b0e
-- title:
--   R: not mem
-- statement:
--   The R construction uses the not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L38-L40
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L38-L40

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.R.not_mem {H : SimpleGraph V} {A Y : Finset V} {w : V} (h : R H A Y w) : w ∉ Y := by sorry
