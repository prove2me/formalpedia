-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_isCap
-- name    : InverseZeroSum.Candidate3.tupleSupportT_isCap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:31.025804+00:00
-- url     : https://prove2.me/theorems/5c24d529-73a4-4b09-819a-0135f6c5db46
-- title:
--   Candidate3: tuple Support T is Cap
-- statement:
--   The Candidate3 construction uses the tuple Support T is Cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1449-L1475
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1449-L1475

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.tupleSupportT_isCap {n : ℕ} (R : PosSeq n) (hFree : ShortFree R) :
    IsCapT (tupleSupportT R) := by sorry
