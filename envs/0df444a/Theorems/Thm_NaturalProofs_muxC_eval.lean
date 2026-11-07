-- Prove2me | Theorems.Thm_NaturalProofs_muxC_eval
-- name    : NaturalProofs.muxC_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:34.739553+00:00
-- url     : https://prove2.me/theorems/8bcd26ae-a844-496f-ad66-c0156129ef15
-- title:
--   Natural Proofs: mux C eval
-- statement:
--   The Natural Proofs construction uses the mux C eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L203-L212
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L203-L212

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

theorem NaturalProofs.muxC_eval (k : ℕ) (s : β ⊕ Bool) (j : Fin k) (z : β ⊕ (Fin k ⊕ Fin (2 * k)) → Bool) :
    (muxC k s j).eval z () =
      if bitval (fun b => z (.inl b)) s then z (.inr (.inr ⟨k + j, by omega⟩))
      else z (.inr (.inr ⟨j, by omega⟩)) := by sorry
