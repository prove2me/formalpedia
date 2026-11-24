-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_shortZero_disjoint_of_ne
-- name    : InverseZeroSum.Candidate3.shortZero_disjoint_of_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:22:33.55015+00:00
-- url     : https://prove2.me/theorems/982de58b-a56b-449c-8c08-69e32bc6be51
-- title:
--   Candidate3: short Zero disjoint of ne
-- statement:
--   For a target-avoiding sequence, distinct short zero-sum positional blocks are
--   disjoint.  Thus the maximal packed family in the S039 source proof may be
--   chosen transparently as the family of all short zero-sum blocks.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L263-L280
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L263-L280

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.shortZero_disjoint_of_ne {n : ℕ} {S : PosSeq n}
    (hAvoid : AvoidsInnerJointPair S) {I J : Finset (Fin n)}
    (hI : ShortZero S I) (hJ : ShortZero S J) (hne : I ≠ J) :
    Disjoint I J := by sorry
