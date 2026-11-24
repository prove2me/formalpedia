-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_cap_inter_plane_le_four
-- name    : InverseZeroSum.Candidate3.cap_inter_plane_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:34.602387+00:00
-- url     : https://prove2.me/theorems/d8afb3cf-3007-44c3-a557-609e2c3fcb89
-- title:
--   Candidate3: cap inter plane le four
-- statement:
--   A cap meets every affine plane in at most four points.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L462-L503
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L462-L503

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.cap_inter_plane_le_four {A : Finset F3T} (hA : IsCapT A) (p : PlaneIdx) :
    (A ∩ planeSetT p).card ≤ 4 := by sorry
