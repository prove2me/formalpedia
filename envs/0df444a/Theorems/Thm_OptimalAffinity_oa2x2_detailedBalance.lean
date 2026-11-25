-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_detailedBalance
-- name    : OptimalAffinity.oa2x2_detailedBalance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:53:22.093193+00:00
-- url     : https://prove2.me/theorems/48460df5-ccf2-588f-aaff-3aee8e9319f5
-- title:
--   Optimal Affinity: oa2x2 detailed Balance
-- statement:
--   The Optimal Affinity construction uses the oa2x2 detailed Balance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L149-L152
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L149-L152

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_detailedBalance : DetailedBalanceExists oa2x2 := by sorry
