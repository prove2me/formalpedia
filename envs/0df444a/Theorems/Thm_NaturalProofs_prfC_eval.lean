-- Prove2me | Theorems.Thm_NaturalProofs_prfC_eval
-- name    : NaturalProofs.prfC_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:00.078205+00:00
-- url     : https://prove2.me/theorems/dddd0d7e-9fc1-46c6-b901-efc3298e6fde
-- title:
--   Natural Proofs: prf C eval
-- statement:
--   The Natural Proofs construction uses the prf C eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L267-L274
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L267-L274

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

theorem NaturalProofs.prfC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (hk : 0 < k) (n : ℕ)
    (s : Bits k) : (prfC gc hk n s).eval = prf G k n s := by sorry
