-- Prove2me | Theorems.Thm_NaturalProofs_genC_size
-- name    : NaturalProofs.genC_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:40.147458+00:00
-- url     : https://prove2.me/theorems/77c5d62c-286a-427e-8fa1-126a2f8be94e
-- title:
--   Natural Proofs: gen C size
-- statement:
--   The Natural Proofs construction uses the gen C size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L186-L188
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L186-L188

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

theorem NaturalProofs.genC_size (k B : ℕ) (hB : ∀ j, (gc k j).size ≤ B) : (genC gc k).size ≤ 2 * k * B := by sorry
