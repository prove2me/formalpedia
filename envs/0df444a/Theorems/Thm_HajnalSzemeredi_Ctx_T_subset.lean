-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_T_subset
-- name    : HajnalSzemeredi.Ctx.T_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:25.821804+00:00
-- url     : https://prove2.me/theorems/2cac1b72-c42f-582b-99a6-c35ccede72bb
-- title:
--   Ctx: T subset
-- statement:
--   The Ctx construction uses the T subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L283-L283
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L283-L283

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

theorem HajnalSzemeredi.Ctx.T_subset (U : ℕ) : T G S P c lo U ⊆ (acc G S P c lo).erase U := by sorry
