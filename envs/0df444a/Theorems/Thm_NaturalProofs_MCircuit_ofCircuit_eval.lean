-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_ofCircuit_eval
-- name    : NaturalProofs.MCircuit.ofCircuit_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:07.901614+00:00
-- url     : https://prove2.me/theorems/fe392cb8-0f10-4699-b01a-65517af1ffe6
-- title:
--   MCircuit: of Circuit eval
-- statement:
--   The MCircuit construction uses the of Circuit eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L154-L155
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L154-L155

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.ofCircuit_eval (C : Circuit α) (x : α → Bool) (u : Unit) :
    (ofCircuit C).eval x u = C.eval x := by sorry
