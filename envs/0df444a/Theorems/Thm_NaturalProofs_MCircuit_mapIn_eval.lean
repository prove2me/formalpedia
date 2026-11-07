-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_mapIn_eval
-- name    : NaturalProofs.MCircuit.mapIn_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:01.994193+00:00
-- url     : https://prove2.me/theorems/3157495c-04c8-480a-b52c-a6f1c1f6a0ac
-- title:
--   MCircuit: map In eval
-- statement:
--   The MCircuit construction uses the map In eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L188-L200
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L188-L200

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.mapIn_eval (f : α → β) (C : MCircuit α γ) (x : β → Bool) (c : γ) :
    (C.mapIn f).eval x c = C.eval (x ∘ f) c := by sorry
