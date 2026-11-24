-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_swap_fixed_complement_zero
-- name    : InverseZeroSum.Candidate3.s9_certificate_swap_fixed_complement_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:19.264423+00:00
-- url     : https://prove2.me/theorems/16d94648-0de1-4aba-bf40-3b36d7c487a5
-- title:
--   Candidate3: s9 certificate swap fixed complement zero
-- statement:
--   In the s=9 zero-sum packing, the eight representatives complementary to a
--   nonconstant packed block must have exactly zero sum.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3338-L3351
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3338-L3351

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s9_certificate_swap_fixed_complement_zero
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 9)
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24} (hy : y ∈ c.blocks j)
    (hVal : S (rep j) ≠ S y) :
    (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
      finiteModelEquiv (S (rep k) : G)) = 0 := by sorry
