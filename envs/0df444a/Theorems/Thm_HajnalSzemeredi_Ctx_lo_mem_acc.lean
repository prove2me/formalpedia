-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_lo_mem_acc
-- name    : HajnalSzemeredi.Ctx.lo_mem_acc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:58.387253+00:00
-- url     : https://prove2.me/theorems/6a658e38-d63e-46ab-bb2a-9956674a6889
-- title:
--   Ctx: lo mem acc
-- statement:
--   The Ctx construction uses the lo mem acc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L91-L92
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L91-L92

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

theorem HajnalSzemeredi.Ctx.lo_mem_acc (h : Ctx G S P c r s lo hi) : lo ∈ acc G S P c lo := by sorry
