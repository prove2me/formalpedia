-- Prove2me | Theorems.Thm_NaturalProofs_Wire_eval_san
-- name    : NaturalProofs.Wire.eval_san
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:18.981805+00:00
-- url     : https://prove2.me/theorems/2de4efd8-5a8f-4ff0-b8ad-54158883f1b7
-- title:
--   Wire: eval san
-- statement:
--   The Wire construction uses the eval san property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L82-L89
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L82-L89

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.Wire.eval_san (x : β → Bool) (acc : List Bool) (w : Wire β) :
    (w.san acc.length).eval x acc = w.eval x acc := by sorry
