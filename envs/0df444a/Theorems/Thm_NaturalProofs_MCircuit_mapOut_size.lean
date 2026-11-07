-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_mapOut_size
-- name    : NaturalProofs.MCircuit.mapOut_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:49.19223+00:00
-- url     : https://prove2.me/theorems/2e1533b7-9878-47a0-8484-3620d9eac0d5
-- title:
--   MCircuit: map Out size
-- statement:
--   The MCircuit construction uses the map Out size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L182-L182
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L182-L182

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.mapOut_size (g : δ → γ) (C : MCircuit α γ) : (C.mapOut g).size = C.size := by sorry
