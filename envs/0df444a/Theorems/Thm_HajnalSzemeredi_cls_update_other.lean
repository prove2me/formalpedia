-- Prove2me | Theorems.Thm_HajnalSzemeredi_cls_update_other
-- name    : HajnalSzemeredi.cls_update_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:15.240418+00:00
-- url     : https://prove2.me/theorems/86fb4f8d-18f6-48a3-8c9a-300447e3f76a
-- title:
--   Hajnal Szemeredi: cls update other
-- statement:
--   The Hajnal Szemeredi construction uses the cls update other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L136-L141
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L136-L141

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
variable {S : Finset V} {c : V → ℕ} {v : V} {j : ℕ}

theorem HajnalSzemeredi.cls_update_other {k : ℕ} (hk : k ≠ j) (hk' : k ≠ c v) :
    cls S (Function.update c v j) k = cls S c k := by sorry
