-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
-- name    : InverseZeroSum.Candidate3.mem_s039AllBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:27.82873+00:00
-- url     : https://prove2.me/theorems/4250a4b4-7f33-462e-b497-e8a4b875771e
-- title:
--   Candidate3: mem s039 All Blocks
-- statement:
--   The Candidate3 construction uses the mem s039 All Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L287-L290
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L287-L290

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.mem_s039AllBlocks {S : PosSeq 24} {I : Finset (Fin 24)} :
    I ∈ s039AllBlocks S ↔ ShortZero S I := by sorry
