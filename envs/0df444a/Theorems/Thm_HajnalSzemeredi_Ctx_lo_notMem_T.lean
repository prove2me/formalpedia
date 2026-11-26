-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_lo_notMem_T
-- name    : HajnalSzemeredi.Ctx.lo_notMem_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:34.027636+00:00
-- url     : https://prove2.me/theorems/c7896496-331e-4db9-9ece-dabc67f5eaf1
-- title:
--   Ctx: lo not Mem T
-- statement:
--   `lo` no está en ningún `T_W`.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L216-L218
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L216-L218

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

theorem HajnalSzemeredi.Ctx.lo_notMem_T (W : ℕ) : lo ∉ T G S P c lo W := by sorry
