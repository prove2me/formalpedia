-- Prove2me | Theorems.Thm_NaturalProofs_Gate_eval_rw
-- name    : NaturalProofs.Gate.eval_rw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:18.841197+00:00
-- url     : https://prove2.me/theorems/fb17e9f2-9794-4efa-8943-63b0933639a8
-- title:
--   Gate: eval rw
-- statement:
--   The Gate construction uses the eval rw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L112-L115
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L112-L115

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.Gate.eval_rw (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (g : Gate α) :
    (g.rw acc.length σ).eval x (acc ++ W) = g.eval (fun a => (σ a).eval x acc) W := by sorry
