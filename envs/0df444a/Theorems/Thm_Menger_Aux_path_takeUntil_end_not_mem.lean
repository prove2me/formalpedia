-- Prove2me | Theorems.Thm_Menger_Aux_path_takeUntil_end_not_mem
-- name    : Menger.Aux.path_takeUntil_end_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:07:52.444741+00:00
-- url     : https://prove2.me/theorems/ab30aeff-9fa5-5262-8f73-f4a708ae5e3a
-- title:
--   Aux: path take Until end not mem
-- statement:
--   The Aux construction uses the path take Until end not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L56-L63
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L56-L63

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.path_takeUntil_end_not_mem [DecidableEq V] {H : SimpleGraph V} {a v w : V}
    (p : H.Walk a v) (hp : p.IsPath) (hw : w ∈ p.support) (hne : w ≠ v) :
    v ∉ (p.takeUntil w hw).support := by sorry
