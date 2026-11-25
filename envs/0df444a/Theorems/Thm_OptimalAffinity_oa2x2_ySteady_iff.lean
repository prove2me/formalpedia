-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_ySteady_iff
-- name    : OptimalAffinity.oa2x2_ySteady_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:55:39.1204+00:00
-- url     : https://prove2.me/theorems/1104db58-017b-5c58-aafa-6381cc3e86b8
-- title:
--   Optimal Affinity: oa2x2 y Steady iff
-- statement:
--   The Optimal Affinity construction uses the oa2x2 y Steady iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Steady.lean#L21-L26
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Steady.lean#L21-L26

module
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Definitions.Def_proofs_OptimalAffinity_Steady
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_ySteady_iff (x y : ℝ) :
    YSteady oa2x2 x y ↔ 3 * x - 2 * y = 7 * y ^ 2 - 6 * x ^ 2 * y := by sorry
