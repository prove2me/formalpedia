-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_horizontalSliceT_eq_inter
-- name    : InverseZeroSum.Candidate3.horizontalSliceT_eq_inter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:23:17.80848+00:00
-- url     : https://prove2.me/theorems/d1f11137-bb84-469f-bd62-29e2e981272d
-- title:
--   Candidate3: horizontal Slice T eq inter
-- statement:
--   The Candidate3 construction uses the horizontal Slice T eq inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L522-L526
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L522-L526

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.horizontalSliceT_eq_inter (A : Finset F3T) (c : Fin 3) :
    horizontalSliceT A c = A ∩ planeSetT (horizontalPlaneT c) := by sorry
