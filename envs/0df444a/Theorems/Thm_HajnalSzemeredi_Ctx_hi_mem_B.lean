-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_hi_mem_B
-- name    : HajnalSzemeredi.Ctx.hi_mem_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:03.644319+00:00
-- url     : https://prove2.me/theorems/c244a215-5d06-45d1-b8ca-fee29077a055
-- title:
--   Ctx: hi mem B
-- statement:
--   The Ctx construction uses the hi mem B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L100-L101
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L100-L101

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

theorem HajnalSzemeredi.Ctx.hi_mem_B (h : Ctx G S P c r s lo hi) : hi ∈ P \ acc G S P c lo := by sorry
