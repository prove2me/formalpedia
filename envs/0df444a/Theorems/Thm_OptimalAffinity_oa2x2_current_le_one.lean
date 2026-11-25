-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_current_le_one
-- name    : OptimalAffinity.oa2x2_current_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:56:44.364791+00:00
-- url     : https://prove2.me/theorems/6229c7e0-a650-4f66-a6cb-7e40200f4afb
-- title:
--   Optimal Affinity: oa2x2 current le one
-- statement:
--   The Optimal Affinity construction uses the oa2x2 current le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/GlobalMaximum.lean#L16-L43
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/GlobalMaximum.lean#L16-L43

module
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_current_le_one
    (x y : ℝ) (hy : 0 < y) (hsteady : YSteady oa2x2 x y) :
    productionCurrent oa2x2 x y ≤ 1 := by sorry
