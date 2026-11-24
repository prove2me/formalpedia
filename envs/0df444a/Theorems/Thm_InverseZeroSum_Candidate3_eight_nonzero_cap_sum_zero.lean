-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_eight_nonzero_cap_sum_zero
-- name    : InverseZeroSum.Candidate3.eight_nonzero_cap_sum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:02.185151+00:00
-- url     : https://prove2.me/theorems/150dcaa2-0dc2-469e-970c-93dc63158a10
-- title:
--   Candidate3: eight nonzero cap sum zero
-- statement:
--   The exact maximal-support invariant required by the length-16 interface.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1853-L1860
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1853-L1860

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.eight_nonzero_cap_sum_zero {A : Finset F3T}
    (hcard : A.card = 8) (hzero : (0 : F3T) ∉ A)
    (hcap : IsCapT (insert 0 A)) :
    (∑ x ∈ A, x) = 0 := by sorry
