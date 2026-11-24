-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_swap_fibre_counts
-- name    : InverseZeroSum.Candidate3.s9_certificate_swap_fibre_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:53.960512+00:00
-- url     : https://prove2.me/theorems/dd118302-6583-4d38-9ec1-61bf70c0539b
-- title:
--   Candidate3: s9 certificate swap fibre counts
-- statement:
--   Exact original-position counts for the two affected fibres under a
--   certificate representative swap, with the symmetric successor cardinality.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2998-L3017
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2998-L3017

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s9_certificate_swap_fibre_counts
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (rep : Fin c.s → Fin 24) (hRep : ∀ j, rep j ∈ c.blocks j)
    (j : Fin c.s) {y : Fin 24}
    (hy : y ∈ c.blocks j) (hxy : rep j ≠ y)
    (v : F3T) :
    ((Finset.univ \ representativeSet (Function.update rep j y)).filter
        (fun i => finiteModelEquiv (S i : G) = v)).card +
      (if finiteModelEquiv (S y : G) = v then 1 else 0) =
    ((Finset.univ \ representativeSet rep).filter
        (fun i => finiteModelEquiv (S i : G) = v)).card +
      (if finiteModelEquiv (S (rep j) : G) = v then 1 else 0) := by sorry
