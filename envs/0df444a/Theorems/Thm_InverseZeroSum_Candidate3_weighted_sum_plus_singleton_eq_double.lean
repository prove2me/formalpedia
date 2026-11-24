-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_weighted_sum_plus_singleton_eq_double
-- name    : InverseZeroSum.Candidate3.weighted_sum_plus_singleton_eq_double
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:34:23.674444+00:00
-- url     : https://prove2.me/theorems/412bcf96-34f5-4399-bb22-ab505dfaa5db
-- title:
--   Candidate3: weighted sum plus singleton eq double
-- statement:
--   Generic support-weight identity: if one support point has weight one and every
--   other support point has weight two, adding the singleton value makes the
--   weighted sum equal the doubled unweighted support sum.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2495-L2511
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2495-L2511

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.weighted_sum_plus_singleton_eq_double
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (A : Finset α) (f : α → M) (w : α → ℕ)
    {u : α} (hu : u ∈ A) (huOne : w u = 1)
    (hOther : ∀ x ∈ A.erase u, w x = 2) :
    (∑ x ∈ A, w x • f x) + f u =
      ∑ x ∈ A, (2 : ℕ) • f x := by sorry
