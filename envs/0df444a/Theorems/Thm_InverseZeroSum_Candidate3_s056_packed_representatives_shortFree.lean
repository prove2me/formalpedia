-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s056_packed_representatives_shortFree
-- name    : InverseZeroSum.Candidate3.s056_packed_representatives_shortFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:02.818802+00:00
-- url     : https://prove2.me/theorems/2f58ad4c-bd15-4b4f-a180-491f6bc6c952
-- title:
--   Candidate3: s056 packed representatives short Free
-- statement:
--   One original-position representative of each packed block forms a short-free
--   sequence: any witness among the representatives would itself have to be a full
--   packed atom, but it meets each packed atom in at most one position.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3527-L3562
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3527-L3562

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s056_packed_representatives_shortFree
    {S : PosSeq 24} (hAvoid : AvoidsInnerJointPair S)
    (c : S039PackingCertificate S)
    (h : S8RepresentativeSwapOutput S c)
    (rep : Fin c.s → Fin 24)
    (hRep : ∀ j, rep j ∈ c.blocks j) :
    ShortFree (fun j => S (rep j)) := by sorry
