-- Prove2me | Theorems.Thm_HajnalSzemeredi_CountHyp_deg_B
-- name    : HajnalSzemeredi.CountHyp.deg_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:47.857753+00:00
-- url     : https://prove2.me/theorems/9a6ed537-1a90-499b-82ac-bae0d226a84d
-- title:
--   Count Hyp: deg B
-- statement:
--   (2.1), forma de grado: `d_B(y) ≤ q - 1` para `y ∈ B`.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean#L176-L182
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean#L176-L182

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

theorem HajnalSzemeredi.CountHyp.deg_B (h : CountHyp G S c PA PB TU r s) {y : V} (hy : y ∈ part S c PB) :
    (nbr G (part S c PB) y).card + 1 ≤ PB.card := by sorry
