-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_nine_cap_direction_slice_pattern
-- name    : InverseZeroSum.Candidate3.nine_cap_direction_slice_pattern
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:36.733458+00:00
-- url     : https://prove2.me/theorems/c8e9373e-5805-42a2-b6d5-62ecd9a0f095
-- title:
--   Candidate3: nine cap direction slice pattern
-- statement:
--   For every direction, a nine-point cap has parallel-plane slice sizes either
--   three-three-three or a permutation of one-four-four.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1724-L1757
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1724-L1757

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.nine_cap_direction_slice_pattern {A : Finset F3T} (hA : IsCapT A)
    (hcard : A.card = 9) (d : Fin 13) :
    ((directionSliceT A d 0).card = 3 ∧
      (directionSliceT A d 1).card = 3 ∧
      (directionSliceT A d 2).card = 3) ∨
    ((directionSliceT A d 0).card = 1 ∧
      (directionSliceT A d 1).card = 4 ∧
      (directionSliceT A d 2).card = 4) ∨
    ((directionSliceT A d 0).card = 4 ∧
      (directionSliceT A d 1).card = 1 ∧
      (directionSliceT A d 2).card = 4) ∨
    ((directionSliceT A d 0).card = 4 ∧
      (directionSliceT A d 1).card = 4 ∧
      (directionSliceT A d 2).card = 1) := by sorry
