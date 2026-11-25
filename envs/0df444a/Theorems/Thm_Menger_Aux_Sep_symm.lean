-- Prove2me | Theorems.Thm_Menger_Aux_Sep_symm
-- name    : Menger.Aux.Sep.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:07:58.065681+00:00
-- url     : https://prove2.me/theorems/3cde830f-5d28-4fbf-b6b2-fd8dd921b1f7
-- title:
--   Sep: symm
-- statement:
--   The Sep construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L29-L32
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L29-L32

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.Sep.symm {G : SimpleGraph V} {A B X : Finset V} (h : Sep G A B X) : Sep G B A X := by sorry
