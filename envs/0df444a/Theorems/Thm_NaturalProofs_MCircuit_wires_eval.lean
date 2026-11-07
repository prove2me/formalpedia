-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_wires_eval
-- name    : NaturalProofs.MCircuit.wires_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:31:06.496185+00:00
-- url     : https://prove2.me/theorems/d688723c-c5ee-4a2c-b39a-ae3ae038cb0f
-- title:
--   MCircuit: wires eval
-- statement:
--   The MCircuit construction uses the wires eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L162-L163
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L162-L163

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.wires_eval (w : γ → Wire α) (x : α → Bool) (c : γ) :
    (wires w).eval x c = (w c).eval x [] := by sorry
