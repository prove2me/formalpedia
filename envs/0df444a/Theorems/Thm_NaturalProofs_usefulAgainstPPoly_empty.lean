-- Prove2me | Theorems.Thm_NaturalProofs_usefulAgainstPPoly_empty
-- name    : NaturalProofs.usefulAgainstPPoly_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:42:34.248466+00:00
-- url     : https://prove2.me/theorems/eaaf8fd2-d8b3-439b-881d-aec1721d6ea3
-- title:
--   Natural Proofs: useful Against PPoly empty
-- statement:
--   The Natural Proofs construction uses the useful Against PPoly empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Sanity.lean#L33-L34
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Sanity.lean#L33-L34

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_Sanity
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs

theorem NaturalProofs.usefulAgainstPPoly_empty : UsefulAgainstPPoly (fun _ => ∅) := by sorry
