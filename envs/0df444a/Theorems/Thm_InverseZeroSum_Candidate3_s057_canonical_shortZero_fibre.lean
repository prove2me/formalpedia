-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s057_canonical_shortZero_fibre
-- name    : InverseZeroSum.Candidate3.s057_canonical_shortZero_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:55.12528+00:00
-- url     : https://prove2.me/theorems/5c5fe5d8-6cf8-4017-ac0e-e3562761c71c
-- title:
--   Candidate3: s057 canonical short Zero fibre
-- statement:
--   Every short zero sum of the canonical triple repetition is precisely
--   one complete three-position base-index fibre.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3840-L3879
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3840-L3879

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s057_canonical_shortZero_fibre
    (U : PosSeq 8) (hInj : Squarefree U) (hFree : ShortFree U)
    {I : Finset (Fin 24)}
    (hShort : ShortZero (tripleRep U) I) :
    ∃ a : Fin 8,
      I = (Finset.univ : Finset (Fin 24)).filter
        (fun i => baseIndex i = a) := by sorry
