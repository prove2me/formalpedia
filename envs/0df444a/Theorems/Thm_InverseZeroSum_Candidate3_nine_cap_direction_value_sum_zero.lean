-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_nine_cap_direction_value_sum_zero
-- name    : InverseZeroSum.Candidate3.nine_cap_direction_value_sum_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:46.961851+00:00
-- url     : https://prove2.me/theorems/da18662d-4800-486a-8d76-2a25c57fb90b
-- title:
--   Candidate3: nine cap direction value sum zero
-- statement:
--   Every affine direction has zero value-sum on a nine-point cap.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1771-L1801
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1771-L1801

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.nine_cap_direction_value_sum_zero {A : Finset F3T} (hA : IsCapT A)
    (hcard : A.card = 9) (d : Fin 13) :
    (∑ x ∈ A, planeValueT d x) = 0 := by sorry
