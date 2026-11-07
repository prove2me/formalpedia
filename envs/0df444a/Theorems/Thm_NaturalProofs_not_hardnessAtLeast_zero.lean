-- Prove2me | Theorems.Thm_NaturalProofs_not_hardnessAtLeast_zero
-- name    : NaturalProofs.not_hardnessAtLeast_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:42:35.539223+00:00
-- url     : https://prove2.me/theorems/04d51c6f-dade-4b5a-b71b-f560cc6b5bbe
-- title:
--   Natural Proofs: not hardness At Least zero
-- statement:
--   The Natural Proofs construction uses the not hardness At Least zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Sanity.lean#L36-L61
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Sanity.lean#L36-L61

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_Sanity
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs

theorem NaturalProofs.not_hardnessAtLeast_zero (k : ℕ) (hk : 0 < k) :
    ¬ HardnessAtLeast (fun _ _ _ => false) k 3 := by sorry
