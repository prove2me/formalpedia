-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_constant_shortZero_block_ne_two
-- name    : InverseZeroSum.Candidate3.constant_shortZero_block_ne_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:41.62103+00:00
-- url     : https://prove2.me/theorems/3c93928b-7c3b-4c53-bb72-cd1d7a40e16b
-- title:
--   Candidate3: constant short Zero block ne two
-- statement:
--   A constant nonzero short zero-sum block cannot have cardinality two.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2189-L2226
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2189-L2226

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.constant_shortZero_block_ne_two {S : PosSeq 24}
    {B : Finset (Fin 24)} (hShort : ShortZero S B)
    (hConst : ∀ x ∈ B, ∀ y ∈ B, S x = S y) :
    B.card ≠ 2 := by sorry
