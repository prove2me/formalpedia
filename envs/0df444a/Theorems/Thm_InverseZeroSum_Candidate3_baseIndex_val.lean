-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
-- name    : InverseZeroSum.Candidate3.baseIndex_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:31.114671+00:00
-- url     : https://prove2.me/theorems/86cdc117-b6ac-456f-bfd7-6dffda40266f
-- title:
--   Candidate3: base Index val
-- statement:
--   The Candidate3 construction uses the base Index val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L187-L188
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L187-L188

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.baseIndex_val (i : Fin 24) :
    (baseIndex i).val = i.val % 8 := by sorry
