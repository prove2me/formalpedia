-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_planePointT_surjective_on
-- name    : InverseZeroSum.Candidate3.planePointT_surjective_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:27:18.117927+00:00
-- url     : https://prove2.me/theorems/e38b4cc9-2d03-4463-8248-5d71a5b416af
-- title:
--   Candidate3: plane Point T surjective on
-- statement:
--   The Candidate3 construction uses the plane Point T surjective on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L407-L410
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L407-L410

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.planePointT_surjective_on :
    ∀ p : PlaneIdx, ∀ x : F3T,
      onPlaneTB p x = true → ∃ q : PlaneCoord, planePointT p q = x := by sorry
