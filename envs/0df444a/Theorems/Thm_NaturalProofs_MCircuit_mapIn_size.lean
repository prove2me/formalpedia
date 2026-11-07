-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_mapIn_size
-- name    : NaturalProofs.MCircuit.mapIn_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:12.769207+00:00
-- url     : https://prove2.me/theorems/026d368f-cff7-49eb-81b0-209ab95fb335
-- title:
--   MCircuit: map In size
-- statement:
--   The MCircuit construction uses the map In size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L202-L203
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L202-L203

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.mapIn_size (f : α → β) (C : MCircuit α γ) : (C.mapIn f).size = C.size := by sorry
