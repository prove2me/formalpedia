-- Prove2me | Theorems.Thm_Menger_Aux_first_use
-- name    : Menger.Aux.first_use
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:10.778461+00:00
-- url     : https://prove2.me/theorems/f592773a-5047-4311-a724-f6680a330098
-- title:
--   Aux: first use
-- statement:
--   The Aux construction uses the first use property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L114-L135
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L114-L135

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.first_use {G : SimpleGraph V} {e : Sym2 V} {A B Y : Finset V}
    (hY : Sep (G.deleteEdges {e}) A B Y) :
    ∀ {u b : V} (q : G.Walk u b), b ∈ B → R (G.deleteEdges {e}) A Y u →
      (∀ w ∈ q.support, w ∉ Y) →
      ∃ z w, G.Adj z w ∧ s(z, w) = e ∧ R (G.deleteEdges {e}) A Y z := by sorry
