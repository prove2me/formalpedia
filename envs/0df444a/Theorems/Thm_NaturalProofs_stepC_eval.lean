-- Prove2me | Theorems.Thm_NaturalProofs_stepC_eval
-- name    : NaturalProofs.stepC_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:45.579854+00:00
-- url     : https://prove2.me/theorems/1afb404b-bd24-41f1-b2f2-bad50e610511
-- title:
--   Natural Proofs: step C eval
-- statement:
--   The Natural Proofs construction uses the step C eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L219-L227
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L219-L227

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

theorem NaturalProofs.stepC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (s : β ⊕ Bool)
    (Cv : MCircuit β (Fin k)) (x : β → Bool) :
    (stepC gc s Cv).eval x = half (bitval x s) (G k (Cv.eval x)) := by sorry
