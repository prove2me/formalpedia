-- Prove2me | Theorems.Thm_HajnalSzemeredi_card_classes_split
-- name    : HajnalSzemeredi.card_classes_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:27.383118+00:00
-- url     : https://prove2.me/theorems/4c09ebee-4920-5745-9acb-b3a9d83b2475
-- title:
--   Hajnal Szemeredi: card classes split
-- statement:
--   The Hajnal Szemeredi construction uses the card classes split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Final.lean#L75-L78
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Final.lean#L75-L78

module
public import Definitions.Def_HajnalSzemeredi_Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_HajnalSzemeredi_Final
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} [Fintype V]

theorem HajnalSzemeredi.card_classes_split {W : Type*} [Fintype W] {p : ℕ} (f : V ⊕ Fin p → W) (i : W) :
    (univ.filter fun w => f w = i).card =
      (univ.filter fun v => f (.inl v) = i).card + (univ.filter fun j => f (.inr j) = i).card := by sorry
