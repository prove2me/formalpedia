-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_on_horizontalPlaneT_iff
-- name    : InverseZeroSum.Candidate3.on_horizontalPlaneT_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:27:28.790796+00:00
-- url     : https://prove2.me/theorems/d1e4d456-3bfa-4638-803d-e20b6444ce87
-- title:
--   Candidate3: on horizontal Plane T iff
-- statement:
--   Membership in the fixed horizontal plane is exactly third-coordinate equality.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L514-L516
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L514-L516

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.on_horizontalPlaneT_iff (c : Fin 3) (x : F3T) :
    onPlaneTB (horizontalPlaneT c) x = true ↔ thirdCoordT x = c := by sorry
