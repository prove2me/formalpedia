-- Prove2me | Theorems.Thm_NaturalProofs_evalGates_eq
-- name    : NaturalProofs.evalGates_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:17.807004+00:00
-- url     : https://prove2.me/theorems/6c5dce52-cec9-4b8d-987f-e325b7854f36
-- title:
--   Natural Proofs: eval Gates eq
-- statement:
--   The Natural Proofs construction uses the eval Gates eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L31-L32
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L31-L32

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.evalGates_eq (x : α → Bool) (gs : List (Gate α)) :
    evalGates x gs = evalFrom x [] gs := by sorry
