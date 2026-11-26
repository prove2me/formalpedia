-- Prove2me | Theorems.Thm_HajnalSzemeredi_sum_card_cls
-- name    : HajnalSzemeredi.sum_card_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:43.410954+00:00
-- url     : https://prove2.me/theorems/80249a47-a824-4232-8864-3309de446069
-- title:
--   Hajnal Szemeredi: sum card cls
-- statement:
--   Las clases de la paleta particionan `S`: la suma de sus tamaños es `|S|`.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L106-L114
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean#L106-L114

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

theorem HajnalSzemeredi.sum_card_cls {S : Finset V} {c : V → ℕ} {P : Finset ℕ} (h : Into S c P) :
    ∑ i ∈ P, (cls S c i).card = S.card := by sorry
