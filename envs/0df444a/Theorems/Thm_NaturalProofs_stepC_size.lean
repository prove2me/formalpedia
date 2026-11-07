-- Prove2me | Theorems.Thm_NaturalProofs_stepC_size
-- name    : NaturalProofs.stepC_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:56.892924+00:00
-- url     : https://prove2.me/theorems/ec9354a7-7b5b-4213-86ca-5bdc055b5dea
-- title:
--   Natural Proofs: step C size
-- statement:
--   The Natural Proofs construction uses the step C size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L229-L234
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L229-L234

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))

theorem NaturalProofs.stepC_size {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (s : β ⊕ Bool)
    (Cv : MCircuit β (Fin k)) : (stepC gc s Cv).size ≤ Cv.size + (2 * k * B + 4 * k) := by sorry
