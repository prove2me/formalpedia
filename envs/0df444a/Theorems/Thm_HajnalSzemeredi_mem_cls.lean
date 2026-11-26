-- Prove2me | Theorems.Thm_HajnalSzemeredi_mem_cls
-- name    : HajnalSzemeredi.mem_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:43:57.787999+00:00
-- url     : https://prove2.me/theorems/340c921e-08f3-4bf1-99e1-2c40dbc59202
-- title:
--   Hajnal Szemeredi: mem cls
-- statement:
--   The Hajnal Szemeredi construction uses the mem cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L89-L91
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L89-L91

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

theorem HajnalSzemeredi.mem_cls {S : Finset V} {c : V → ℕ} {i : ℕ} {v : V} :
    v ∈ cls S c i ↔ v ∈ S ∧ c v = i := by sorry
