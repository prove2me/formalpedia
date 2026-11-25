-- Prove2me | Theorems.Thm_Menger_Aux_Fam_mono
-- name    : Menger.Aux.Fam.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:12.910744+00:00
-- url     : https://prove2.me/theorems/a115539b-8f30-40d3-85b8-9b2f46faf548
-- title:
--   Fam: mono
-- statement:
--   The Fam construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L86-L93
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L86-L93

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.Fam.mono {G G' : SimpleGraph V} (hle : G ≤ G') {A B : Finset V} {k : ℕ}
    (h : Fam G A B k) : Fam G' A B k := by sorry
