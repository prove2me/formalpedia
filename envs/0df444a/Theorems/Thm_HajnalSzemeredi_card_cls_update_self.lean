-- Prove2me | Theorems.Thm_HajnalSzemeredi_card_cls_update_self
-- name    : HajnalSzemeredi.card_cls_update_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:20.96493+00:00
-- url     : https://prove2.me/theorems/d1be190e-dd9d-4717-ad4e-9236eed6f158
-- title:
--   Hajnal Szemeredi: card cls update self
-- statement:
--   The Hajnal Szemeredi construction uses the card cls update self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L143-L146
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L143-L146

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

theorem HajnalSzemeredi.card_cls_update_self (hv : v ∈ S) (hj : c v ≠ j) :
    (cls S (Function.update c v j) j).card = (cls S c j).card + 1 := by sorry
