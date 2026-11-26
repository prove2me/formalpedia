-- Prove2me | Theorems.Thm_HajnalSzemeredi_CountHyp_card_Sy
-- name    : HajnalSzemeredi.CountHyp.card_Sy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:45.296377+00:00
-- url     : https://prove2.me/theorems/6a7254bd-7bc3-468d-a514-71fe3d123e73
-- title:
--   Count Hyp: card Sy
-- statement:
--   Desigualdad (2.3): `|S^y| ≥ t - q + 1 + d_B(y)`.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean#L147-L173
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean#L147-L173

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_HajnalSzemeredi_Count
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
open HajnalSzemeredi.CountHyp
variable {S : Finset V} {c : V → ℕ} {PA PB TU : Finset ℕ} {r s : ℕ}

theorem HajnalSzemeredi.CountHyp.card_Sy (h : CountHyp G S c PA PB TU r s) {y : V} (hy : y ∈ part S c PB) :
    TU.card + 1 + (nbr G (part S c PB) y).card ≤
      (Sy G S c TU (part S c PB) y).card + PB.card := by sorry
