-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_representative_sum_eq_total_of_residual_zero
-- name    : InverseZeroSum.Candidate3.representative_sum_eq_total_of_residual_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:23.820863+00:00
-- url     : https://prove2.me/theorems/b7570892-306c-4ecb-9d2f-dbb001e8a755
-- title:
--   Candidate3: representative sum eq total of residual zero
-- statement:
--   If a representative-deletion residual sums to zero, the selected
--   representatives sum to the total sum of the original sequence.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2071-L2088
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2071-L2088

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.representative_sum_eq_total_of_residual_zero {s : ℕ}
    (S : PosSeq 24) {blocks : Fin s → Finset (Fin 24)}
    {rep : Fin s → Fin 24}
    (hBlocks : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hRep : ∀ j, rep j ∈ blocks j)
    (hResidualZero :
      posSum S (Finset.univ \ representativeSet rep) = 0) :
    (∑ j : Fin s, (S (rep j) : G)) = totalSum S := by sorry
