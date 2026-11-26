-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_countHyp
-- name    : HajnalSzemeredi.Ctx.countHyp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:25.262033+00:00
-- url     : https://prove2.me/theorems/8bda9f79-8e3f-46f7-ace9-33fffb7ec6cf
-- title:
--   Ctx: count Hyp
-- statement:
--   Las hipótesis de conteo valen para `𝒜' = T_U`.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L286-L318
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L286-L318

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

theorem HajnalSzemeredi.Ctx.countHyp (h : Ctx G S P c r s lo hi) {U : ℕ} (hU : U ∈ acc G S P c lo)
    (hne : (T G S P c lo U).Nonempty)
    (hP2 : ∀ X ∈ T G S P c lo U, ∀ Y ∈ acc G S P c lo, Y ∉ T G S P c lo U → Y ≠ U →
      ¬ Mov G S c X Y) :
    CountHyp G S c (acc G S P c lo) (P \ acc G S P c lo) (T G S P c lo U) r s := by sorry
