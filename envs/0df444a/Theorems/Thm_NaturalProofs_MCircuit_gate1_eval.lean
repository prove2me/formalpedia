-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_gate1_eval
-- name    : NaturalProofs.MCircuit.gate1_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:36:22.766203+00:00
-- url     : https://prove2.me/theorems/b04b4db6-3645-4ed5-83dc-32bc4d1021e7
-- title:
--   MCircuit: gate1 eval
-- statement:
--   The MCircuit construction uses the gate1 eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L170-L172
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L170-L172

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.gate1_eval (g : Gate α) (x : α → Bool) (u : Unit) :
    (gate1 g).eval x u = g.eval x [] := by sorry
