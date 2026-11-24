-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_survivor_swap
-- name    : InverseZeroSum.Candidate3.s9_certificate_survivor_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:08.572799+00:00
-- url     : https://prove2.me/theorems/534c4094-a77e-4790-8e05-708825b500ff
-- title:
--   Candidate3: s9 certificate survivor swap
-- statement:
--   The survivor sets of two certificate transversals differing at one packed
--   block exchange exactly the two selected original positions.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2943-L2994
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2943-L2994

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s9_certificate_survivor_swap
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24}
    (hy : y ∈ c.blocks j) (hxy : rep j ≠ y) :
    (Finset.univ \
        representativeSet (Function.update rep j y)) =
      insert (rep j)
        ((Finset.univ \ representativeSet rep).erase y) ∧
    y ∈ (Finset.univ \ representativeSet rep) ∧
    rep j ∉ (Finset.univ \ representativeSet rep) := by sorry
