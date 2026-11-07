-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_ofCircuit_size
-- name    : NaturalProofs.MCircuit.ofCircuit_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:47.10337+00:00
-- url     : https://prove2.me/theorems/251ddbaf-c78e-4ade-8c58-5bcfcbffecfb
-- title:
--   MCircuit: of Circuit size
-- statement:
--   The MCircuit construction uses the of Circuit size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L157-L157
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L157-L157

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.ofCircuit_size (C : Circuit α) : (ofCircuit C).size = C.size := by sorry
