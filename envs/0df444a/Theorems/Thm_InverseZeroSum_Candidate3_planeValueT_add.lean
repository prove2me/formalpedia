-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_planeValueT_add
-- name    : InverseZeroSum.Candidate3.planeValueT_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:43.802114+00:00
-- url     : https://prove2.me/theorems/a13a7f2a-5cd7-4133-af99-97f2516c9067
-- title:
--   Candidate3: plane Value T add
-- statement:
--   The explicit plane direction forms are additive.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1804-L1809
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1804-L1809

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.planeValueT_add :
    ∀ d : Fin 13, ∀ x y : F3T,
      planeValueT d (x + y) = planeValueT d x + planeValueT d y := by sorry
