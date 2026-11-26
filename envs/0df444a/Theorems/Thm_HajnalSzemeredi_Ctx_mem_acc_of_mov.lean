-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_mem_acc_of_mov
-- name    : HajnalSzemeredi.Ctx.mem_acc_of_mov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:02.035456+00:00
-- url     : https://prove2.me/theorems/98148a80-1088-4368-bd33-9f5fa5b08062
-- title:
--   Ctx: mem acc of mov
-- statement:
--   The Ctx construction uses the mem acc of mov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L94-L98
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L94-L98

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

theorem HajnalSzemeredi.Ctx.mem_acc_of_mov (h : Ctx G S P c r s lo hi) {a b : ℕ} (hab : Mov G S c a b)
    (hb : b ∈ acc G S P c lo) : a ∈ acc G S P c lo := by sorry
