-- Prove2me | Theorems.Thm_NaturalProofs_evalFrom_append
-- name    : NaturalProofs.evalFrom_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:35.892977+00:00
-- url     : https://prove2.me/theorems/38517f5d-0009-4437-8a82-a1815811820f
-- title:
--   Natural Proofs: eval From append
-- statement:
--   The Natural Proofs construction uses the eval From append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L34-L36
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L34-L36

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.evalFrom_append (x : α → Bool) (acc : List Bool) (gs₁ gs₂ : List (Gate α)) :
    evalFrom x acc (gs₁ ++ gs₂) = evalFrom x (evalFrom x acc gs₁) gs₂ := by sorry
