-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_shortZero_subset_eq
-- name    : InverseZeroSum.Candidate3.shortZero_subset_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:25:23.18809+00:00
-- url     : https://prove2.me/theorems/204d5a8c-e19c-42c8-88cb-2ab8f91a0b35
-- title:
--   Candidate3: short Zero subset eq
-- statement:
--   Over the nonzero alphabet in exponent three, a short zero-sum positional block
--   has no proper nonempty zero-sum subblock.  This is the minimality fact used by
--   the packed-atom source proof.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L234-L255
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L234-L255

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.shortZero_subset_eq {n : ℕ} {S : PosSeq n}
    {I J : Finset (Fin n)} (hI : ShortZero S I) (hJ : ShortZero S J)
    (hsub : I ⊆ J) : I = J := by sorry
