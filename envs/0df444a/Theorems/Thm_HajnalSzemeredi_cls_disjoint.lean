-- Prove2me | Theorems.Thm_HajnalSzemeredi_cls_disjoint
-- name    : HajnalSzemeredi.cls_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:43:58.40494+00:00
-- url     : https://prove2.me/theorems/fea58246-6552-4155-80ec-f210986fd820
-- title:
--   Hajnal Szemeredi: cls disjoint
-- statement:
--   The Hajnal Szemeredi construction uses the cls disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L98-L103
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L98-L103

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

theorem HajnalSzemeredi.cls_disjoint {S : Finset V} {c : V → ℕ} {i j : ℕ} (h : i ≠ j) :
    Disjoint (cls S c i) (cls S c j) := by sorry
