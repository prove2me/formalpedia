-- Prove2me | Theorems.Thm_HajnalSzemeredi_mem_nbr
-- name    : HajnalSzemeredi.mem_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:43:58.920461+00:00
-- url     : https://prove2.me/theorems/de4b30ba-6d64-4d09-b151-d041a781e344
-- title:
--   Hajnal Szemeredi: mem nbr
-- statement:
--   The Hajnal Szemeredi construction uses the mem nbr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L95-L96
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L95-L96

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} (G : SimpleGraph V)
variable {G}

theorem HajnalSzemeredi.mem_nbr {S : Finset V} {v w : V} : w ∈ nbr G S v ↔ w ∈ S ∧ G.Adj v w := by sorry
