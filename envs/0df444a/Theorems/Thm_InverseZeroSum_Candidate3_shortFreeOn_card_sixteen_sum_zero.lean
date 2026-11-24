-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_shortFreeOn_card_sixteen_sum_zero
-- name    : InverseZeroSum.Candidate3.shortFreeOn_card_sixteen_sum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:30.828807+00:00
-- url     : https://prove2.me/theorems/03a963bc-a347-4fc7-9300-3eee63e1d417
-- title:
--   Candidate3: short Free On card sixteen sum zero
-- statement:
--   Faithfully reindex a sixteen-position surviving set as a positional sequence.
--   The universal short-freeness-on-the-survivors hypothesis then feeds the closed
--   length-16 sum-zero interface.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2012-L2044
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2012-L2044

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.shortFreeOn_card_sixteen_sum_zero
    (h16 : Length16SumZeroInput) (S : PosSeq 24)
    {A : Finset (Fin 24)} (hCard : A.card = 16)
    (hFree : ShortFreeOn S A) :
    posSum S A = 0 := by sorry
