-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_directionSliceT_eq_inter
-- name    : InverseZeroSum.Candidate3.directionSliceT_eq_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:33.216041+00:00
-- url     : https://prove2.me/theorems/7078b459-c473-442f-852c-792dfe2de617
-- title:
--   Candidate3: direction Slice T eq inter
-- statement:
--   The Candidate3 construction uses the direction Slice T eq inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1700-L1704
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1700-L1704

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.directionSliceT_eq_inter (A : Finset F3T) (d : Fin 13) (c : Fin 3) :
    directionSliceT A d c = A ∩ planeSetT (d, c) := by sorry
