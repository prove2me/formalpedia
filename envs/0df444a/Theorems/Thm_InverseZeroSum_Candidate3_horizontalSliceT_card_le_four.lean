-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_horizontalSliceT_card_le_four
-- name    : InverseZeroSum.Candidate3.horizontalSliceT_card_le_four
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:27:18.178147+00:00
-- url     : https://prove2.me/theorems/c781b48f-e450-435b-bf00-c3065a34d33a
-- title:
--   Candidate3: horizontal Slice T card le four
-- statement:
--   The Candidate3 construction uses the horizontal Slice T card le four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L528-L531
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L528-L531

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.horizontalSliceT_card_le_four {A : Finset F3T} (hA : IsCapT A) (c : Fin 3) :
    (horizontalSliceT A c).card ≤ 4 := by sorry
