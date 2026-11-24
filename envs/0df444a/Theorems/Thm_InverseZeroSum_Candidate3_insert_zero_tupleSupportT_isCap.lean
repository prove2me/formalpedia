-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_insert_zero_tupleSupportT_isCap
-- name    : InverseZeroSum.Candidate3.insert_zero_tupleSupportT_isCap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:44.656362+00:00
-- url     : https://prove2.me/theorems/78805104-1b55-48c7-b1c0-d069d028f88d
-- title:
--   Candidate3: insert zero tuple Support T is Cap
-- statement:
--   The Candidate3 construction uses the insert zero tuple Support T is Cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1505-L1534
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1505-L1534

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.insert_zero_tupleSupportT_isCap {n : ℕ} (R : PosSeq n)
    (hFree : ShortFree R) :
    IsCapT (insert 0 (tupleSupportT R)) := by sorry
