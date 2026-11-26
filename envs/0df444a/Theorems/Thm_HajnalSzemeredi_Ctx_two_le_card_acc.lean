-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_two_le_card_acc
-- name    : HajnalSzemeredi.Ctx.two_le_card_acc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:12.146329+00:00
-- url     : https://prove2.me/theorems/fcda6db6-fe62-58f4-a486-7acfb9f810a7
-- title:
--   Ctx: two le card acc
-- statement:
--   `|𝒜| ≥ 2`.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L167-L213
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L167-L213

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

theorem HajnalSzemeredi.Ctx.two_le_card_acc (h : Ctx G S P c r s lo hi) : 2 ≤ (acc G S P c lo).card := by sorry
