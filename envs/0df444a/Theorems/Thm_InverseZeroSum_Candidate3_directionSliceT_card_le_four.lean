-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_directionSliceT_card_le_four
-- name    : InverseZeroSum.Candidate3.directionSliceT_card_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:35.952317+00:00
-- url     : https://prove2.me/theorems/3c293d22-892f-4249-af3a-e966a102f6a5
-- title:
--   Candidate3: direction Slice T card le four
-- statement:
--   The Candidate3 construction uses the direction Slice T card le four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1706-L1710
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1706-L1710

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.directionSliceT_card_le_four {A : Finset F3T} (hA : IsCapT A)
    (d : Fin 13) (c : Fin 3) :
    (directionSliceT A d c).card ≤ 4 := by sorry
