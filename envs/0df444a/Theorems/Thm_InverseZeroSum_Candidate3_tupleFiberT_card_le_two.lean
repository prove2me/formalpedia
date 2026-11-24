-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_le_two
-- name    : InverseZeroSum.Candidate3.tupleFiberT_card_le_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:22:23.068952+00:00
-- url     : https://prove2.me/theorems/94a4e78c-a07d-45d2-b944-d27aa327bce9
-- title:
--   Candidate3: tuple Fiber T card le two
-- statement:
--   The Candidate3 construction uses the tuple Fiber T card le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1536-L1571
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1536-L1571

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.tupleFiberT_card_le_two {n : ℕ} (R : PosSeq n) (hFree : ShortFree R) :
    ∀ x ∈ tupleSupportT R,
      ((Finset.univ : Finset (Fin n)).filter
        (fun i => tupleValueT R i = x)).card ≤ 2 := by sorry
