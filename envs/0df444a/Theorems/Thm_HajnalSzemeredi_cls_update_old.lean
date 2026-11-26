-- Prove2me | Theorems.Thm_HajnalSzemeredi_cls_update_old
-- name    : HajnalSzemeredi.cls_update_old
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:10.918807+00:00
-- url     : https://prove2.me/theorems/a2ae5732-20de-581f-b7d6-57a7b694202b
-- title:
--   Hajnal Szemeredi: cls update old
-- statement:
--   The Hajnal Szemeredi construction uses the cls update old property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L129-L134
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L129-L134

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

theorem HajnalSzemeredi.cls_update_old (hv : v ∈ S) (hj : c v ≠ j) :
    cls S (Function.update c v j) (c v) = (cls S c (c v)).erase v := by sorry
