-- Prove2me | Theorems.Thm_Menger_Aux_R_of_mem
-- name    : Menger.Aux.R.of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:07:48.269872+00:00
-- url     : https://prove2.me/theorems/25130fd0-e332-580b-815e-abd5b3fd83f4
-- title:
--   R: of mem
-- statement:
--   The R construction uses the of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L42-L44
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L42-L44

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.R.of_mem {H : SimpleGraph V} {A Y : Finset V} {w : V} (hw : w ∈ A) (hY : w ∉ Y) :
    R H A Y w := by sorry
