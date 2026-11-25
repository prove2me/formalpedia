-- Prove2me | Theorems.Thm_Menger_Aux_sep_transfer
-- name    : Menger.Aux.sep_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:30.37681+00:00
-- url     : https://prove2.me/theorems/12a8ef70-0133-5939-95ba-0c22ec387f81
-- title:
--   Aux: sep transfer
-- statement:
--   The Aux construction uses the sep transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L155-L202
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/MengerCore.lean#L155-L202

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}

theorem Menger.Aux.sep_transfer [DecidableEq V] {G : SimpleGraph V} {e : Sym2 V} {x y : V} (he : s(x, y) = e)
    {A B Y Z : Finset V} (hY : Sep (G.deleteEdges {e}) A B Y)
    (hy : ¬ R (G.deleteEdges {e}) A Y y)
    (hZ : Sep (G.deleteEdges {e}) A (insert x Y) Z) : Sep G A B Z := by sorry
