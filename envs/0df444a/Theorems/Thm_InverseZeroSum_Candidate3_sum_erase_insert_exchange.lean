-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_sum_erase_insert_exchange
-- name    : InverseZeroSum.Candidate3.sum_erase_insert_exchange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:53.392091+00:00
-- url     : https://prove2.me/theorems/6d191914-e938-406d-ab62-1a9bcfec5bf7
-- title:
--   Candidate3: sum erase insert exchange
-- statement:
--   Additive sum balance for exchanging one old and one new survivor.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2876-L2892
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2876-L2892

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.sum_erase_insert_exchange
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (A : Finset α) (f : α → M) {x y : α}
    (hx : x ∉ A) (hy : y ∈ A) :
    (∑ i ∈ insert x (A.erase y), f i) + f y =
      (∑ i ∈ A, f i) + f x := by sorry
