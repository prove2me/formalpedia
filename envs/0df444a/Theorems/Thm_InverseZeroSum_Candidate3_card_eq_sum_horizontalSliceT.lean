-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_card_eq_sum_horizontalSliceT
-- name    : InverseZeroSum.Candidate3.card_eq_sum_horizontalSliceT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:28:17.875038+00:00
-- url     : https://prove2.me/theorems/e5bd7fee-bbbc-4f3b-848e-a8ad6dba653e
-- title:
--   Candidate3: card eq sum horizontal Slice T
-- statement:
--   The Candidate3 construction uses the card eq sum horizontal Slice T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L533-L539
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L533-L539

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.card_eq_sum_horizontalSliceT (A : Finset F3T) :
    A.card = ∑ c : Fin 3, (horizontalSliceT A c).card := by sorry
