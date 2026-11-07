-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_parAll_size_le
-- name    : NaturalProofs.MCircuit.parAll_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:42.491195+00:00
-- url     : https://prove2.me/theorems/60fbd8fe-be6e-460f-b2ed-81dd9ac62996
-- title:
--   MCircuit: par All size le
-- statement:
--   The MCircuit construction uses the par All size le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L304-L308
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L304-L308

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.parAll_size_le [Fintype α] [DecidableEq α] (E : α → MCircuit β Unit) (B : ℕ)
    (hE : ∀ a, (E a).size ≤ B) : (parAll E).size ≤ Fintype.card α * B := by sorry
