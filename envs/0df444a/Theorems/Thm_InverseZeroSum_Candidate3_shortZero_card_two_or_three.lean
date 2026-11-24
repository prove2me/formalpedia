-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_shortZero_card_two_or_three
-- name    : InverseZeroSum.Candidate3.shortZero_card_two_or_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:36.666803+00:00
-- url     : https://prove2.me/theorems/9311910d-c5dc-4f66-93e2-498317534007
-- title:
--   Candidate3: short Zero card two or three
-- statement:
--   The Candidate3 construction uses the short Zero card two or three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L206-L215
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L206-L215

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.shortZero_card_two_or_three {n : ℕ} {S : PosSeq n}
    {I : Finset (Fin n)} (h : ShortZero S I) :
    I.card = 2 ∨ I.card = 3 := by sorry
