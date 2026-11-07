-- Prove2me | Theorems.Thm_NaturalProofs_leafC_eval
-- name    : NaturalProofs.leafC_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:23.16239+00:00
-- url     : https://prove2.me/theorems/387fcd76-04d3-498f-b87e-396c512bfd23
-- title:
--   Natural Proofs: leaf C eval
-- statement:
--   The Natural Proofs construction uses the leaf C eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L306-L314
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L306-L314

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

theorem NaturalProofs.leafC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k n : ℕ} (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (x : Fin n → Bool)
    (y : Fin (2 * k) → Bool) :
    (leafC gc hk i e c x).eval y () = hybF G (i + 1) (expand (Function.update c e y)) x := by sorry
