-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_comp_eval
-- name    : NaturalProofs.MCircuit.comp_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:31:14.994717+00:00
-- url     : https://prove2.me/theorems/5171422e-4e3b-40ed-a1c9-eeee299d7394
-- title:
--   MCircuit: comp eval
-- statement:
--   The MCircuit construction uses the comp eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L258-L261
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L258-L261

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.comp_eval (C : MCircuit α γ) (E : MCircuit β α) (x : β → Bool) (c : γ) :
    (C.comp E).eval x c = C.eval (E.eval x) c := by sorry
