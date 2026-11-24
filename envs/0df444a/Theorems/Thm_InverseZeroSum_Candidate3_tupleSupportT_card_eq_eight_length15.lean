-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_card_eq_eight_length15
-- name    : InverseZeroSum.Candidate3.tupleSupportT_card_eq_eight_length15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:53.052752+00:00
-- url     : https://prove2.me/theorems/7fb83499-dc52-4c5d-a39f-705b4458c194
-- title:
--   Candidate3: tuple Support T card eq eight length15
-- statement:
--   A short-free length-15 sequence has exactly eight tuple support values.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2277-L2292
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2277-L2292

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.tupleSupportT_card_eq_eight_length15 (R : PosSeq 15)
    (hFree : ShortFree R) :
    (tupleSupportT R).card = 8 := by sorry
