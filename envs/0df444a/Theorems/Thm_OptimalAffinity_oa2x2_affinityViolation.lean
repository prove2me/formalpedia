-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_affinityViolation
-- name    : OptimalAffinity.oa2x2_affinityViolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:57:20.477882+00:00
-- url     : https://prove2.me/theorems/a8f4c4f1-3773-50c1-bea0-11f1e632ad3e
-- title:
--   Optimal Affinity: oa2x2 affinity Violation
-- statement:
--   The Optimal Affinity construction uses the oa2x2 affinity Violation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L25-L27
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L25-L27

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_affinityViolation : affinityExp oa2x2 1 1 < seedRatio oa2x2 := by sorry
