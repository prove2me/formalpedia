-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_toCircuit_eval
-- name    : NaturalProofs.MCircuit.toCircuit_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:58.346789+00:00
-- url     : https://prove2.me/theorems/b9694f6f-1f71-4e10-a54c-d277e71d739b
-- title:
--   MCircuit: to Circuit eval
-- statement:
--   The MCircuit construction uses the to Circuit eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L146-L147
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L146-L147

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.toCircuit_eval (C : MCircuit α γ) (c : γ) (x : α → Bool) :
    (C.toCircuit c).eval x = C.eval x c := by sorry
