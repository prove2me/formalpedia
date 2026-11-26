-- Prove2me | Theorems.Thm_HajnalSzemeredi_CountHyp_lemma_2_3
-- name    : HajnalSzemeredi.CountHyp.lemma_2_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:54.213965+00:00
-- url     : https://prove2.me/theorems/c018adb2-ae82-43d3-aa05-34c41328e0cd
-- title:
--   Count Hyp: lemma 2 3
-- statement:
--   **Lema 2.3.** Existe un vértice solo `z` (con color en `TU`) que es movible a otra clase de
--   `PA`, o que tiene dos vecinos especiales distintos no adyacentes.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean#L244-L339
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean#L244-L339

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

theorem HajnalSzemeredi.CountHyp.lemma_2_3 (h : CountHyp G S c PA PB TU r s) :
    ∃ z ∈ S, c z ∈ TU ∧ (Sz G S c TU (part S c PB) z).Nonempty ∧
      ((∃ X ∈ PA, X ≠ c z ∧ Movable G S c z X) ∨
        ∃ y₁ ∈ Sz G S c TU (part S c PB) z, ∃ y₂ ∈ Sz G S c TU (part S c PB) z,
          y₁ ≠ y₂ ∧ ¬ G.Adj y₁ y₂) := by sorry
