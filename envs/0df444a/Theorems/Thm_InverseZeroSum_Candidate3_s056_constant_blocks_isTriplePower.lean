-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s056_constant_blocks_isTriplePower
-- name    : InverseZeroSum.Candidate3.s056_constant_blocks_isTriplePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:41.319884+00:00
-- url     : https://prove2.me/theorems/db33f2b6-3f7d-4e8f-9872-be79dad7805a
-- title:
--   Candidate3: s056 constant blocks is Triple Power
-- statement:
--   Enumerate the three positions in each of the eight disjoint constant atoms
--   and use division/modulo eight to produce the exact commutative-sequence
--   permutation witness, rather than fixing the original order.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3659-L3713
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3659-L3713

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s056_constant_blocks_isTriplePower
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 8) (hConst : S8RepresentativeSwapOutput S c)
    (rep : Fin c.s → Fin 24)
    (hRep : ∀ j, rep j ∈ c.blocks j) :
    IsTriplePower S (fun i : Fin 8 => S (rep (Fin.cast hs.symm i))) := by sorry
