-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_shortZero_two_block_has_distinct_values
-- name    : InverseZeroSum.Candidate3.shortZero_two_block_has_distinct_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:02.698806+00:00
-- url     : https://prove2.me/theorems/cfa4a09e-5694-47de-8139-ede3c506ceeb
-- title:
--   Candidate3: short Zero two block has distinct values
-- statement:
--   A zero-sum two-block on the nonzero alphabet is nonconstant.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2895-L2905
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2895-L2905

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.shortZero_two_block_has_distinct_values
    {S : PosSeq 24} {B : Finset (Fin 24)}
    (hShort : ShortZero S B) (hCard : B.card = 2) :
    ∃ x ∈ B, ∃ y ∈ B, S x ≠ S y := by sorry
