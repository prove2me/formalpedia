-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_planePointT_sum_zero_of_coord
-- name    : InverseZeroSum.Candidate3.planePointT_sum_zero_of_coord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:27:21.337654+00:00
-- url     : https://prove2.me/theorems/866a704d-a550-415f-9484-6a7685bac82b
-- title:
--   Candidate3: plane Point T sum zero of coord
-- statement:
--   The affine parametrisation preserves three-term zero sums.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L447-L453
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L447-L453

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.planePointT_sum_zero_of_coord :
    ∀ p : PlaneIdx, ∀ a b c : PlaneCoord,
      a + b + c = 0 →
      planePointT p a + planePointT p b + planePointT p c = 0 := by sorry
