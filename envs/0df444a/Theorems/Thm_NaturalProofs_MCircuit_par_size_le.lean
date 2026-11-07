-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_par_size_le
-- name    : NaturalProofs.MCircuit.par_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:43.492214+00:00
-- url     : https://prove2.me/theorems/a8c7c1de-f75d-4552-acfd-8591049504e8
-- title:
--   MCircuit: par size le
-- statement:
--   The MCircuit construction uses the par size le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L287-L294
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L287-L294

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.par_size_le [DecidableEq α] (E : α → MCircuit β Unit) (l : List α) (B : ℕ)
    (hE : ∀ a, (E a).size ≤ B) : (par E l).size ≤ l.length * B := by sorry
