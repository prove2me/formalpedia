-- Prove2me | Theorems.Thm_NaturalProofs_distC_eval
-- name    : NaturalProofs.distC_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:34.321139+00:00
-- url     : https://prove2.me/theorems/c30a35aa-22b6-4e21-83b3-6c6552b79413
-- title:
--   Natural Proofs: dist C eval
-- statement:
--   The Natural Proofs construction uses the dist C eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L323-L330
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L323-L330

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

theorem NaturalProofs.distC_eval (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k n : ℕ} (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (D : Circuit (Fin n → Bool))
    (y : Fin (2 * k) → Bool) :
    (distC gc hk i e c D).eval y = D.eval (hybF G (i + 1) (expand (Function.update c e y))) := by sorry
