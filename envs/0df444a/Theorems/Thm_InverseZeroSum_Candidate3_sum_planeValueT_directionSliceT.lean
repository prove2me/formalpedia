-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_sum_planeValueT_directionSliceT
-- name    : InverseZeroSum.Candidate3.sum_planeValueT_directionSliceT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:44.09028+00:00
-- url     : https://prove2.me/theorems/7dffe658-0161-4885-8a14-494a2329060c
-- title:
--   Candidate3: sum plane Value T direction Slice T
-- statement:
--   The Candidate3 construction uses the sum plane Value T direction Slice T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1759-L1768
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1759-L1768

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.sum_planeValueT_directionSliceT (A : Finset F3T) (d : Fin 13)
    (c : Fin 3) :
    (∑ x ∈ directionSliceT A d c, planeValueT d x) =
      (directionSliceT A d c).card • c := by sorry
