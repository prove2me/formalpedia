-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_zero_not_mem_tupleSupportT
-- name    : InverseZeroSum.Candidate3.zero_not_mem_tupleSupportT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:35.102288+00:00
-- url     : https://prove2.me/theorems/b7b2cc66-0733-4d68-b56a-0d8354a56100
-- title:
--   Candidate3: zero not mem tuple Support T
-- statement:
--   The Candidate3 construction uses the zero not mem tuple Support T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1440-L1447
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1440-L1447

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.zero_not_mem_tupleSupportT {n : ℕ} (R : PosSeq n) :
    (0 : F3T) ∉ tupleSupportT R := by sorry
