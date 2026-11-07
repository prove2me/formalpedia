-- Prove2me | Theorems.Thm_NaturalProofs_length_evalGates
-- name    : NaturalProofs.length_evalGates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:46.102196+00:00
-- url     : https://prove2.me/theorems/d5adcb9f-f0e8-404b-8d49-a4d8278a6ce1
-- title:
--   Natural Proofs: length eval Gates
-- statement:
--   The Natural Proofs construction uses the length eval Gates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L48-L50
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L48-L50

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.length_evalGates (x : α → Bool) (gs : List (Gate α)) :
    (evalGates x gs).length = gs.length := by sorry
