-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_reactant_invertible
-- name    : OptimalAffinity.oa2x2_reactant_invertible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:03:57.82169+00:00
-- url     : https://prove2.me/theorems/39745058-4a70-476c-9c08-06739789dec0
-- title:
--   Optimal Affinity: oa2x2 reactant invertible
-- statement:
--   The Optimal Affinity construction uses the oa2x2 reactant invertible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L20-L22
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L20-L22

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section

theorem OptimalAffinity.oa2x2_reactant_invertible : reactantDet oa2x2 ≠ 0 := by sorry
