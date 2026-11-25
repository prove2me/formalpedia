-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_optimalAffinityExp
-- name    : OptimalAffinity.oa2x2_optimalAffinityExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:57:30.339387+00:00
-- url     : https://prove2.me/theorems/1802258e-bdda-504e-af02-a488ade275d9
-- title:
--   Optimal Affinity: oa2x2 optimal Affinity Exp
-- statement:
--   The Optimal Affinity construction uses the oa2x2 optimal Affinity Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L19-L20
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L19-L20

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_optimalAffinityExp : affinityExp oa2x2 1 1 = 7 / 4 := by sorry
