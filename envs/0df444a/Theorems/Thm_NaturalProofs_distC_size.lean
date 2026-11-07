-- Prove2me | Theorems.Thm_NaturalProofs_distC_size
-- name    : NaturalProofs.distC_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:31.427089+00:00
-- url     : https://prove2.me/theorems/736c49b9-07e9-455e-86e1-556f6a76142b
-- title:
--   Natural Proofs: dist C size
-- statement:
--   The Natural Proofs construction uses the dist C size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L332-L349
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L332-L349

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

theorem NaturalProofs.distC_size {k n B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (D : Circuit (Fin n → Bool)) :
    (distC gc hk i e c D).size ≤ 2 ^ n * (n * (2 * k * B + 4 * k)) + D.size := by sorry
