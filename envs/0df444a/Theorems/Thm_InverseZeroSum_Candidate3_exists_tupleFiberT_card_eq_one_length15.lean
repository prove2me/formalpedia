-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_exists_tupleFiberT_card_eq_one_length15
-- name    : InverseZeroSum.Candidate3.exists_tupleFiberT_card_eq_one_length15
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:23:41.513928+00:00
-- url     : https://prove2.me/theorems/006d3504-f9fe-4e8d-9aa3-0396a22536ea
-- title:
--   Candidate3: exists tuple Fiber T card eq one length15
-- statement:
--   A short-free length-15 sequence has a support value occurring exactly once.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2295-L2350
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2295-L2350

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.exists_tupleFiberT_card_eq_one_length15 (R : PosSeq 15)
    (hFree : ShortFree R) :
    ∃ u ∈ tupleSupportT R,
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = u)).card = 1 := by sorry
