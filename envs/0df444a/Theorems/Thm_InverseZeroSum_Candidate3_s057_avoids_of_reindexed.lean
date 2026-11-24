-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s057_avoids_of_reindexed
-- name    : InverseZeroSum.Candidate3.s057_avoids_of_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:32:01.486644+00:00
-- url     : https://prove2.me/theorems/e31400ab-0e2e-431b-aecd-0eb6cc32521e
-- title:
--   Candidate3: s057 avoids of reindexed
-- statement:
--   Avoidance is invariant under the exact original-position permutation:
--   pull a witness back by the inverse equivalence, apply avoidance, and transport
--   the indexed intersection sum through the same bijection.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3913-L3942
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3913-L3942

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s057_avoids_of_reindexed (S : PosSeq 24)
    (e : Fin 24 ≃ Fin 24)
    (hAvoid : AvoidsInnerJointPair (fun i => S (e i))) :
    AvoidsInnerJointPair S := by sorry
