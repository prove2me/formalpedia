-- Prove2me | Theorems.Thm_Menger_Aux_orient
-- name    : Menger.Aux.orient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:07.771876+00:00
-- url     : https://prove2.me/theorems/8ea265bf-814a-5b14-9fc4-3a9b15e90a8e
-- title:
--   Aux: orient
-- statement:
--   The Aux construction uses the orient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L137-L153
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L137-L153

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.orient {G : SimpleGraph V} {e : Sym2 V} {A B Y : Finset V}
    (hY : Sep (G.deleteEdges {e}) A B Y) (hG : ¬ Sep G A B Y) :
    ∃ x y, G.Adj x y ∧ s(x, y) = e ∧ R (G.deleteEdges {e}) A Y x ∧
      R (G.deleteEdges {e}) B Y y := by sorry
