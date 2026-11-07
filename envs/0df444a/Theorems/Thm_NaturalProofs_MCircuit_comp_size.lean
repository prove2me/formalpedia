-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_comp_size
-- name    : NaturalProofs.MCircuit.comp_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:31:30.466804+00:00
-- url     : https://prove2.me/theorems/96f148ce-1100-4ee6-bbc3-0335c7e0d274
-- title:
--   MCircuit: comp size
-- statement:
--   The MCircuit construction uses the comp size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L263-L265
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L263-L265

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.comp_size (C : MCircuit α γ) (E : MCircuit β α) :
    (C.comp E).size = E.size + C.size := by sorry
