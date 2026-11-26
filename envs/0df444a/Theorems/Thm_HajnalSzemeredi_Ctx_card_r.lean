-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_card_r
-- name    : HajnalSzemeredi.Ctx.card_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:01.770364+00:00
-- url     : https://prove2.me/theorems/007dbbb7-3661-5b03-bc28-4f886202eb07
-- title:
--   Ctx: card r
-- statement:
--   The Ctx construction uses the card r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L109-L114
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L109-L114

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
open HajnalSzemeredi.Ctx
variable {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ}

theorem HajnalSzemeredi.Ctx.card_r (h : Ctx G S P c r s lo hi) :
    r + 1 = (acc G S P c lo).card + (P \ acc G S P c lo).card := by sorry
