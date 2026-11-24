-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s057_base_double_plus_zero
-- name    : InverseZeroSum.Candidate3.s057_base_double_plus_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:45.583858+00:00
-- url     : https://prove2.me/theorems/96430acc-3f90-4358-9d6c-b35d41bc0d0f
-- title:
--   Candidate3: s057 base double plus zero
-- statement:
--   In exponent three, a three-term zero sum containing the same nonzero
--   base value twice must have that same value in its remaining position.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3786-L3801
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3786-L3801

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s057_base_double_plus_zero
    (U : PosSeq 8) (hInj : Squarefree U)
    (a b : Fin 8)
    (hZero : (U a : G) + (U a : G) + (U b : G) = 0) :
    a = b := by sorry
