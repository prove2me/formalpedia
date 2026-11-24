-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_s057_baseIndex_fibre_card
-- name    : InverseZeroSum.Candidate3.s057_baseIndex_fibre_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:52.240585+00:00
-- url     : https://prove2.me/theorems/1158b7ed-3e18-41dd-aa46-337d5843421f
-- title:
--   Candidate3: s057 base Index fibre card
-- statement:
--   Exactly three canonical positions reduce modulo eight to any fixed base
--   index; this is a small transparent arithmetic count, not an orbit catalogue.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3833-L3836
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L3833-L3836

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000

theorem InverseZeroSum.Candidate3.s057_baseIndex_fibre_card (a : Fin 8) :
    ((Finset.univ : Finset (Fin 24)).filter
      (fun i => baseIndex i = a)).card = 3 := by sorry
