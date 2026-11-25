-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_netEntries
-- name    : OptimalAffinity.oa2x2_netEntries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:53:25.156409+00:00
-- url     : https://prove2.me/theorems/8d4764bf-886c-5b18-ab2b-d1420de56cbc
-- title:
--   Optimal Affinity: oa2x2 net Entries
-- statement:
--   The Optimal Affinity construction uses the oa2x2 net Entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L126-L129
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Source.lean#L126-L129

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_netEntries :
    netX oa2x2 0 = -1 ∧ netX oa2x2 1 = 2 ∧
    netY oa2x2 0 = 1 ∧ netY oa2x2 1 = -1 := by sorry
