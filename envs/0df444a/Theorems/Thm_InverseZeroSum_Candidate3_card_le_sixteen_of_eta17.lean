-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_card_le_sixteen_of_eta17
-- name    : InverseZeroSum.Candidate3.card_le_sixteen_of_eta17
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:17.238058+00:00
-- url     : https://prove2.me/theorems/b3fbb555-91b8-490a-aa03-baf8f2bd2178
-- title:
--   Candidate3: card le sixteen of eta17
-- statement:
--   The published eta(C_3^3)=17 source interface bounds any short-free set of
--   positions in a length-24 positional sequence by 16.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1023-L1039
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1023-L1039

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.card_le_sixteen_of_eta17 (hEta : Eta17Input)
    (S : PosSeq 24) {A : Finset (Fin 24)} (hFree : ShortFreeOn S A) :
    A.card ≤ 16 := by sorry
