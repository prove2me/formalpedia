-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_tupleValueT_sum_eq_support_weight
-- name    : InverseZeroSum.Candidate3.tupleValueT_sum_eq_support_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:52.817773+00:00
-- url     : https://prove2.me/theorems/cd1fcd0a-4114-4fd2-adc0-2d74d2affc00
-- title:
--   Candidate3: tuple Value T sum eq support weight
-- statement:
--   Group a positional tuple sum by its support fibres.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2450-L2487
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2450-L2487

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.tupleValueT_sum_eq_support_weight {n : ℕ} (R : PosSeq n) :
    (∑ i ∈ (Finset.univ : Finset (Fin n)), tupleValueT R i) =
      ∑ x ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin n)).filter
          (fun i => tupleValueT R i = x)).card • x := by sorry
