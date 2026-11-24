-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_length15_singleton_sum_identity
-- name    : InverseZeroSum.Candidate3.length15_singleton_sum_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:22.26595+00:00
-- url     : https://prove2.me/theorems/40cf41e9-5b6a-42ba-87a6-ea512bb83c10
-- title:
--   Candidate3: length15 singleton sum identity
-- statement:
--   For a short-free length-15 residual with a singleton support value, the total
--   tuple sum plus that value is zero. This preserves the full S040 information:
--   the nonzero-total interface alone would discard the singleton's identity.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2595-L2647
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2595-L2647

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.length15_singleton_sum_identity
    (R : PosSeq 15) (hFree : ShortFree R)
    {u : F3T} (hu : u ∈ tupleSupportT R)
    (huOne :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = u)).card = 1) :
    (∑ i ∈ (Finset.univ : Finset (Fin 15)), tupleValueT R i) + u = 0 := by sorry
