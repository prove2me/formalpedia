-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_planeValueT_sum
-- name    : InverseZeroSum.Candidate3.planeValueT_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:52.433674+00:00
-- url     : https://prove2.me/theorems/135a653f-6eee-46d5-9b37-6b6677332b12
-- title:
--   Candidate3: plane Value T sum
-- statement:
--   The Candidate3 construction uses the plane Value T sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1815-L1822
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1815-L1822

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.planeValueT_sum (d : Fin 13) (A : Finset F3T) :
    planeValueT d (∑ x ∈ A, x) = ∑ x ∈ A, planeValueT d x := by sorry
