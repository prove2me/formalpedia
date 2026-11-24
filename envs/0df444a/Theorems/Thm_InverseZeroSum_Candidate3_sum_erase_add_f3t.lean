-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_sum_erase_add_f3t
-- name    : InverseZeroSum.Candidate3.sum_erase_add_f3t
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:33:57.503853+00:00
-- url     : https://prove2.me/theorems/a457d692-be94-4bc3-b286-ea26995f1ed3
-- title:
--   Candidate3: sum erase add f3t
-- statement:
--   Sum decomposition at one erased point, specialized to the tuple codomain.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2444-L2447
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2444-L2447

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.sum_erase_add_f3t {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → F3T) {a : α} (ha : a ∈ A) :
    (∑ x ∈ A.erase a, f x) + f a = ∑ x ∈ A, f x := by sorry
