-- Prove2me | Theorems.Thm_Menger_Aux_R_disj
-- name    : Menger.Aux.R_disj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:07:55.766087+00:00
-- url     : https://prove2.me/theorems/ff36093d-a256-4aa2-93b5-932ebbc7923d
-- title:
--   Aux: R disj
-- statement:
--   The Aux construction uses the R disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L46-L54
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L46-L54

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.R_disj {H : SimpleGraph V} {A B Y : Finset V} (hY : Sep H A B Y) {w : V}
    (hA : R H A Y w) (hB : R H B Y w) : False := by sorry
