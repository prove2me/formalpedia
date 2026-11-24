-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_planeValueT_sub
-- name    : InverseZeroSum.Candidate3.planeValueT_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:28:13.108805+00:00
-- url     : https://prove2.me/theorems/be671877-a8d9-43ba-871a-3126dabe1eda
-- title:
--   Candidate3: plane Value T sub
-- statement:
--   The explicit direction forms are additive.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L551-L554
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L551-L554

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.planeValueT_sub :
    ∀ d : Fin 13, ∀ x y : F3T,
      planeValueT d (x - y) = planeValueT d x - planeValueT d y := by sorry
