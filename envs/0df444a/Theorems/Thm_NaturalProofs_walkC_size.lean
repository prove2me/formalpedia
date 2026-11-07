-- Prove2me | Theorems.Thm_NaturalProofs_walkC_size
-- name    : NaturalProofs.walkC_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:38.528049+00:00
-- url     : https://prove2.me/theorems/9df5661d-b598-4e9e-b83c-102a1eb434d5
-- title:
--   Natural Proofs: walk C size
-- statement:
--   The Natural Proofs construction uses the walk C size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L251-L260
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L251-L260

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

theorem NaturalProofs.walkC_size {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (Cv : MCircuit β (Fin k))
    (ss : List (β ⊕ Bool)) :
    (walkC gc Cv ss).size ≤ Cv.size + ss.length * (2 * k * B + 4 * k) := by sorry
