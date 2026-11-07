-- Prove2me | Theorems.Thm_NaturalProofs_Wire_eval_rw
-- name    : NaturalProofs.Wire.eval_rw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:35.829725+00:00
-- url     : https://prove2.me/theorems/a96c9835-bf1f-427d-b026-99c20182ca7a
-- title:
--   Wire: eval rw
-- statement:
--   The Wire construction uses the eval rw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L99-L110
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L99-L110

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.Wire.eval_rw (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (w : Wire α) :
    (w.rw acc.length σ).eval x (acc ++ W) = w.eval (fun a => (σ a).eval x acc) W := by sorry
