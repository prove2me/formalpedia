-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s057_base_triple_zero
-- name    : InverseZeroSum.Candidate3.s057_base_triple_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:51.801031+00:00
-- url     : https://prove2.me/theorems/a9074d41-50f4-49b5-8c10-07c7fd49d3e8
-- title:
--   Candidate3: s057 base triple zero
-- statement:
--   Three base values from a squarefree short-free sequence can sum to zero
--   only when all three indices coincide.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3805-L3828
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3805-L3828

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s057_base_triple_zero
    (U : PosSeq 8) (hInj : Squarefree U) (hFree : ShortFree U)
    (a b c : Fin 8)
    (hZero : (U a : G) + (U b : G) + (U c : G) = 0) :
    a = b ∧ b = c := by sorry
