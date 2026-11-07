-- Prove2me | Theorems.Thm_NaturalProofs_expand_bijective
-- name    : NaturalProofs.expand_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:04.872484+00:00
-- url     : https://prove2.me/theorems/77f640e5-f708-41a2-8b63-286936d355c0
-- title:
--   Natural Proofs: expand bijective
-- statement:
--   The Natural Proofs construction uses the expand bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L98-L104
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L98-L104

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

theorem NaturalProofs.expand_bijective (k i : ℕ) :
    Function.Bijective (expand : ((Fin i → Bool) → Fin (2 * k) → Bool) → _ → Bits k) := by sorry
