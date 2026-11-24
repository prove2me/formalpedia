-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_eq_two_length16
-- name    : InverseZeroSum.Candidate3.tupleFiberT_card_eq_two_length16
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:14.178531+00:00
-- url     : https://prove2.me/theorems/40607719-2e87-4b8b-9036-227e689d8647
-- title:
--   Candidate3: tuple Fiber T card eq two length16
-- statement:
--   Every support value of a short-free length-16 sequence occurs exactly twice.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1882-L1942
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1882-L1942

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.tupleFiberT_card_eq_two_length16 (R : PosSeq 16)
    (hFree : ShortFree R) :
    ∀ x ∈ tupleSupportT R,
      ((Finset.univ : Finset (Fin 16)).filter
        (fun i => tupleValueT R i = x)).card = 2 := by sorry
