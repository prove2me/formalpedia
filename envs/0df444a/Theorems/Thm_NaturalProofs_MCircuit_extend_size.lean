-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_extend_size
-- name    : NaturalProofs.MCircuit.extend_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:24.826475+00:00
-- url     : https://prove2.me/theorems/3ba4500d-3e47-4911-9425-339f1f009018
-- title:
--   MCircuit: extend size
-- statement:
--   The MCircuit construction uses the extend size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L216-L218
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L216-L218

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.extend_size (E : MCircuit β α) (C : MCircuit (β ⊕ α) γ) :
    (extend E C).size = E.size + C.size := by sorry
