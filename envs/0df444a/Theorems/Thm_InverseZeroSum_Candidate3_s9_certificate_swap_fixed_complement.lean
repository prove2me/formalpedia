-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_swap_fixed_complement
-- name    : InverseZeroSum.Candidate3.s9_certificate_swap_fixed_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:14.300929+00:00
-- url     : https://prove2.me/theorems/77ff7a2f-badd-499e-8e4a-b1366fce8d0d
-- title:
--   Candidate3: s9 certificate swap fixed complement
-- statement:
--   Every nonconstant packed block in an s=9 certificate fixes the sum of the
--   other eight selected representatives to the full packed-sequence sum.
--   The forbidden (0,1) transition is eliminated by the two singleton equations.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3188-L3289
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3188-L3289

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s9_certificate_swap_fixed_complement
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 9)
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24} (hy : y ∈ c.blocks j)
    (hVal : S (rep j) ≠ S y) :
    (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
      finiteModelEquiv (S (rep k) : G)) =
    ∑ i : Fin 24, finiteModelEquiv (S i : G) := by sorry
