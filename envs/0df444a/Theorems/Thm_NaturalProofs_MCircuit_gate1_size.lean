-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_gate1_size
-- name    : NaturalProofs.MCircuit.gate1_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:36:50.103297+00:00
-- url     : https://prove2.me/theorems/31bf1e04-a962-4480-87e7-e2845393c811
-- title:
--   MCircuit: gate1 size
-- statement:
--   The MCircuit construction uses the gate1 size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L174-L174
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L174-L174

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.gate1_size (g : Gate α) : (gate1 g).size = 1 := by sorry
