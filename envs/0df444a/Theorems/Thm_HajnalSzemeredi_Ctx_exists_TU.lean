-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_exists_TU
-- name    : HajnalSzemeredi.Ctx.exists_TU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:22.687109+00:00
-- url     : https://prove2.me/theorems/da819322-2013-4650-8538-d82c36ec0233
-- title:
--   Ctx: exists TU
-- statement:
--   Elección de `U` y de la familia `𝒜' = T_U`.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L232-L281
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L232-L281

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

theorem HajnalSzemeredi.Ctx.exists_TU (h : Ctx G S P c r s lo hi) :
    ∃ U ∈ acc G S P c lo, (T G S P c lo U).Nonempty ∧
      (∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
        ReflTransGen (avoid G S c W) X lo) ∧
      (∀ X ∈ T G S P c lo U, ∀ Y ∈ acc G S P c lo, Y ∉ T G S P c lo U → Y ≠ U →
        ¬ Mov G S c X Y) := by sorry
