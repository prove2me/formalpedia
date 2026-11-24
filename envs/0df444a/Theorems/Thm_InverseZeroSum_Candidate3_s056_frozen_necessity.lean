-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s056_frozen_necessity
-- name    : InverseZeroSum.Candidate3.s056_frozen_necessity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:31:40.937965+00:00
-- url     : https://prove2.me/theorems/c61fd7fc-5667-4d8b-9ed9-058694181f09
-- title:
--   Candidate3: s056 frozen necessity
-- statement:
--   Frozen iff, necessity half: the previously checked proof spine together
--   with the original-position three-block permutation yields the exact structural
--   normal form, without using any sufficiency statement.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3719-L3757
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3719-L3757

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s056_frozen_necessity (S : PosSeq 24)
    (hAvoid : AvoidsInnerJointPair S) :
    ∃ U : PosSeq 8,
      Squarefree U ∧ ShortFree U ∧ IsTriplePower S U := by sorry
