-- Prove2me | Theorems.Thm_HajnalSzemeredi_CountHyp_lemma_2_2
-- name    : HajnalSzemeredi.CountHyp.lemma_2_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:42.653492+00:00
-- url     : https://prove2.me/theorems/fda57f32-05ae-58ca-8cf3-2b9c71d6070f
-- title:
--   Count Hyp: lemma 2 2
-- statement:
--   **Lema 2.2.** Si ningún vértice solo de `W ∈ TU` es movible a otra clase de `PA`, entonces
--   `q + 1 ≤ t` y todo `y ∈ B` es solo.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean#L186-L240
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean#L186-L240

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

theorem HajnalSzemeredi.CountHyp.lemma_2_2 (h : CountHyp G S c PA PB TU r s) {W : ℕ} (hW : W ∈ TU)
    (hW' : ∀ z ∈ cls S c W, (Sz G S c TU (part S c PB) z).Nonempty →
      ∀ X ∈ PA, X ≠ W → ¬ Movable G S c z X) :
    PB.card + 1 ≤ TU.card ∧ ∀ y ∈ part S c PB, (Sy G S c TU (part S c PB) y).Nonempty := by sorry
