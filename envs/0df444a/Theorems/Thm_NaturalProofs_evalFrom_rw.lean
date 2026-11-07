-- Prove2me | Theorems.Thm_NaturalProofs_evalFrom_rw
-- name    : NaturalProofs.evalFrom_rw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:18.26867+00:00
-- url     : https://prove2.me/theorems/5bb1d710-dbb7-4b9c-8f1e-c5541814a933
-- title:
--   Natural Proofs: eval From rw
-- statement:
--   The Natural Proofs construction uses the eval From rw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L117-L125
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L117-L125

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.evalFrom_rw (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (gs : List (Gate α)) :
    evalFrom x (acc ++ W) (gs.map (Gate.rw acc.length σ)) =
      acc ++ evalFrom (fun a => (σ a).eval x acc) W gs := by sorry
