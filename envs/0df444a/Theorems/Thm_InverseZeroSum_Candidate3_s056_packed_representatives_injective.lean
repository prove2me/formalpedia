-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s056_packed_representatives_injective
-- name    : InverseZeroSum.Candidate3.s056_packed_representatives_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:24:02.830861+00:00
-- url     : https://prove2.me/theorems/c307de22-fa56-422f-a4a8-e4084470aaac
-- title:
--   Candidate3: s056 packed representatives injective
-- statement:
--   Representatives of different constant packed three-blocks carry distinct
--   values: otherwise replacing one position in a packed atom by a point from the
--   other block constructs an overlapping short zero sum.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3568-L3618
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3568-L3618

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s056_packed_representatives_injective
    {S : PosSeq 24} (hAvoid : AvoidsInnerJointPair S)
    (c : S039PackingCertificate S) (hs : c.s = 8)
    (h : S8RepresentativeSwapOutput S c)
    (rep : Fin c.s → Fin 24)
    (hRep : ∀ j, rep j ∈ c.blocks j) :
    Function.Injective (fun j => S (rep j)) := by sorry
