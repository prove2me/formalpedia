-- Prove2me | Theorems.Thm_HajnalSzemeredi_cls_subset
-- name    : HajnalSzemeredi.cls_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:38.987912+00:00
-- url     : https://prove2.me/theorems/0c4822b3-269a-504c-815e-666b935994aa
-- title:
--   Hajnal Szemeredi: cls subset
-- statement:
--   The Hajnal Szemeredi construction uses the cls subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L93-L93
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L93-L93

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

theorem HajnalSzemeredi.cls_subset (S : Finset V) (c : V → ℕ) (i : ℕ) : cls S c i ⊆ S := by sorry
