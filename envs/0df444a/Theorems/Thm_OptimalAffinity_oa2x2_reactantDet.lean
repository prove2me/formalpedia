-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_reactantDet
-- name    : OptimalAffinity.oa2x2_reactantDet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:03:25.128237+00:00
-- url     : https://prove2.me/theorems/dc398c64-381f-5d58-9d9f-937f92f18cd1
-- title:
--   Optimal Affinity: oa2x2 reactant Det
-- statement:
--   The Optimal Affinity construction uses the oa2x2 reactant Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L17-L18
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L17-L18

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section

theorem OptimalAffinity.oa2x2_reactantDet : reactantDet oa2x2 = 2 := by sorry
