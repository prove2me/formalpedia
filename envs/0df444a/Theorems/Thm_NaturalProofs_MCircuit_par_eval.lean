-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_par_eval
-- name    : NaturalProofs.MCircuit.par_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:37.603092+00:00
-- url     : https://prove2.me/theorems/f4c40c60-8d3f-4627-b72e-379c4f10e171
-- title:
--   MCircuit: par eval
-- statement:
--   The MCircuit construction uses the par eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L275-L285
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L275-L285

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.par_eval [DecidableEq α] (E : α → MCircuit β Unit) (l : List α) (x : β → Bool)
    (b : α) (hb : b ∈ l) : (par E l).eval x b = (E b).eval x () := by sorry
