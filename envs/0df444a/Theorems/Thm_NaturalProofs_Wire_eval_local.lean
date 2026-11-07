-- Prove2me | Theorems.Thm_NaturalProofs_Wire_eval_local
-- name    : NaturalProofs.Wire.eval_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:28.682506+00:00
-- url     : https://prove2.me/theorems/cb2651f9-5f29-4951-b2c4-fb1bbeb84674
-- title:
--   Wire: eval local
-- statement:
--   The Wire construction uses the eval local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L91-L97
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L91-L97

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.Wire.eval_local (x : β → Bool) (acc W : List Bool) (w : Wire β)
    (h : w.Local acc.length) : w.eval x (acc ++ W) = w.eval x acc := by sorry
