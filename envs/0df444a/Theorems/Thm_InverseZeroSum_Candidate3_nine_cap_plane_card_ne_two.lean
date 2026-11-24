-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_nine_cap_plane_card_ne_two
-- name    : InverseZeroSum.Candidate3.nine_cap_plane_card_ne_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:27.551163+00:00
-- url     : https://prove2.me/theorems/6e833362-9f52-4dae-9941-6ab2dc17839c
-- title:
--   Candidate3: nine cap plane card ne two
-- statement:
--   A nine-point cap cannot meet an affine plane in exactly two points.
--   If it did, the four planes through those two points would cover the ambient
--   space.  The distinguished plane contains no further cap point, while each of
--   the other three contains at most two further cap points, leaving room for at
--   most eight cap points in total.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1596-L1694
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1596-L1694

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.nine_cap_plane_card_ne_two {A : Finset F3T} (hA : IsCapT A)
    (hcard : A.card = 9) (H : PlaneIdx) :
    (A ∩ planeSetT H).card ≠ 2 := by sorry
