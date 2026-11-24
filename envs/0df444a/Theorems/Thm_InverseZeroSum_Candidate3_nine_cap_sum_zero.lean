-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_nine_cap_sum_zero
-- name    : InverseZeroSum.Candidate3.nine_cap_sum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:57.334843+00:00
-- url     : https://prove2.me/theorems/309ec4c1-410e-40b7-b0a5-d665646a000d
-- title:
--   Candidate3: nine cap sum zero
-- statement:
--   Every nine-point cap in the tuple model has total point-sum zero.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1825-L1850
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1825-L1850

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.nine_cap_sum_zero {A : Finset F3T} (hA : IsCapT A)
    (hcard : A.card = 9) :
    (∑ x ∈ A, x) = 0 := by sorry
