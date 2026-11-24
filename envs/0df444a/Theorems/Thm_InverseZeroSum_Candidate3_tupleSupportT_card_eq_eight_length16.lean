-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_card_eq_eight_length16
-- name    : InverseZeroSum.Candidate3.tupleSupportT_card_eq_eight_length16
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:23:41.639808+00:00
-- url     : https://prove2.me/theorems/c41c609a-41fd-403a-8b09-ce89ee690dfd
-- title:
--   Candidate3: tuple Support T card eq eight length16
-- statement:
--   A short-free length-16 sequence uses exactly eight tuple support values.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1864-L1879
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1864-L1879

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.tupleSupportT_card_eq_eight_length16 (R : PosSeq 16)
    (hFree : ShortFree R) :
    (tupleSupportT R).card = 8 := by sorry
