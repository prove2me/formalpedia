-- Prove2me | Theorems.Thm_HajnalSzemeredi_card_part
-- name    : HajnalSzemeredi.card_part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:49.545213+00:00
-- url     : https://prove2.me/theorems/6bd0eca2-b493-528a-96cb-2f276eef0d31
-- title:
--   Hajnal Szemeredi: card part
-- statement:
--   The Hajnal Szemeredi construction uses the card part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L54-L61
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L54-L61

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}

theorem HajnalSzemeredi.card_part (S : Finset V) (c : V → ℕ) (Q : Finset ℕ) :
    (part S c Q).card = ∑ i ∈ Q, (cls S c i).card := by sorry
