-- Prove2me | Theorems.Thm_NaturalProofs_expand_injective
-- name    : NaturalProofs.expand_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:32:58.587645+00:00
-- url     : https://prove2.me/theorems/25d08633-a8c3-4312-a8b0-123c3a2a99e1
-- title:
--   Natural Proofs: expand injective
-- statement:
--   The Natural Proofs construction uses the expand injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L86-L96
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L86-L96

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

theorem NaturalProofs.expand_injective (k i : ℕ) :
    Function.Injective (expand : ((Fin i → Bool) → Fin (2 * k) → Bool) → _ → Bits k) := by sorry
