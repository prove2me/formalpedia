-- Prove2me | Theorems.Thm_NaturalProofs_MCircuit_extend_eval
-- name    : NaturalProofs.MCircuit.extend_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:41.155319+00:00
-- url     : https://prove2.me/theorems/0d53ffee-b2f6-438e-a3ef-825cae5add77
-- title:
--   MCircuit: extend eval
-- statement:
--   The MCircuit construction uses the extend eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L220-L252
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L220-L252

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit

theorem NaturalProofs.MCircuit.extend_eval (E : MCircuit β α) (C : MCircuit (β ⊕ α) γ) (x : β → Bool) :
    (extend E C).eval x =
      Sum.elim (E.eval x) (C.eval (Sum.elim x (E.eval x))) := by sorry
