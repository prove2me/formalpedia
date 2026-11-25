-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_logAffinityViolation
-- name    : OptimalAffinity.oa2x2_logAffinityViolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:00.497787+00:00
-- url     : https://prove2.me/theorems/411c76ba-a911-44ca-9b0b-a04cbe4bb901
-- title:
--   Optimal Affinity: oa2x2 log Affinity Violation
-- statement:
--   The Optimal Affinity construction uses the oa2x2 log Affinity Violation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L29-L30
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L29-L30

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_logAffinityViolation : Real.log (7 / 4 : ℝ) < Real.log 2 := by sorry
