-- Prove2me | Theorems.Thm_NaturalProofs_length_evalFrom
-- name    : NaturalProofs.length_evalFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:45.196222+00:00
-- url     : https://prove2.me/theorems/34929279-ffc6-43c4-9dba-78f76161a465
-- title:
--   Natural Proofs: length eval From
-- statement:
--   The Natural Proofs construction uses the length eval From property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L38-L46
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Circuits.lean#L38-L46

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}

theorem NaturalProofs.length_evalFrom (x : α → Bool) (acc : List Bool) (gs : List (Gate α)) :
    (evalFrom x acc gs).length = acc.length + gs.length := by sorry
