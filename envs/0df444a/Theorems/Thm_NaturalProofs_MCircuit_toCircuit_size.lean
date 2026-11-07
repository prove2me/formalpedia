-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_toCircuit_size
-- name    : NaturalProofs.MCircuit.toCircuit_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:16.68422+00:00
-- url     : https://prove2.me/theorems/5cf52878-54c3-4b38-992c-d9cf25cd3fb6
-- title:
--   MCircuit: to Circuit size
-- statement:
--   The MCircuit construction uses the to Circuit size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L149-L149
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L149-L149

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.toCircuit_size (C : MCircuit α γ) (c : γ) : (C.toCircuit c).size = C.size := by sorry
