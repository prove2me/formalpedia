-- Prove2me | Theorems.Thm_HajnalSzemeredi_Ctx_h21
-- name    : HajnalSzemeredi.Ctx.h21
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:20.285714+00:00
-- url     : https://prove2.me/theorems/7e8fe1c7-f4c3-4fd6-a367-5bb86ca24678
-- title:
--   Ctx: h21
-- statement:
--   (2.1): todo vértice de `B` tiene un vecino en cada clase accesible.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L117-L127
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean#L117-L127

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

theorem HajnalSzemeredi.Ctx.h21 (h : Ctx G S P c r s lo hi) {y : V} (hy : y ∈ part S c (P \ acc G S P c lo))
    {X : ℕ} (hX : X ∈ acc G S P c lo) : (nIn G S c y X).Nonempty := by sorry
