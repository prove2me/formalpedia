-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_current_eq_one_iff
-- name    : OptimalAffinity.oa2x2_current_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:56:22.310402+00:00
-- url     : https://prove2.me/theorems/03490361-45a9-5d4d-89c3-0c5d8cc3550c
-- title:
--   Optimal Affinity: oa2x2 current eq one iff
-- statement:
--   The Optimal Affinity construction uses the oa2x2 current eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/GlobalMaximum.lean#L45-L70
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/GlobalMaximum.lean#L45-L70

module
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_current_eq_one_iff
    (x y : ℝ) (hy : 0 < y) (hsteady : YSteady oa2x2 x y) :
    productionCurrent oa2x2 x y = 1 ↔ x = 1 ∧ y = 1 := by sorry
