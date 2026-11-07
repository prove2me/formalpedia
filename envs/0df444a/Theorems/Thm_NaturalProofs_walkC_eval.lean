-- Prove2me | Theorems.Thm_NaturalProofs_walkC_eval
-- name    : NaturalProofs.walkC_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:36.805576+00:00
-- url     : https://prove2.me/theorems/3679dd09-44f8-4016-9b42-1c0450f1a2d4
-- title:
--   Natural Proofs: walk C eval
-- statement:
--   The Natural Proofs construction uses the walk C eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L241-L249
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L241-L249

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

theorem NaturalProofs.walkC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (Cv : MCircuit β (Fin k))
    (ss : List (β ⊕ Bool)) (x : β → Bool) :
    (walkC gc Cv ss).eval x = walk G (Cv.eval x) (ss.map (bitval x)) := by sorry
