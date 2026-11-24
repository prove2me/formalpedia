-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_shortZero_map_pullSeq
-- name    : InverseZeroSum.Candidate3.shortZero_map_pullSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:28.533016+00:00
-- url     : https://prove2.me/theorems/4089fc24-056c-4d5c-8342-fc4e5647f977
-- title:
--   Candidate3: short Zero map pull Seq
-- statement:
--   A short zero sum survives transport along an injective map of positions.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L223-L227
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L223-L227

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.shortZero_map_pullSeq {m n : ℕ} (S : PosSeq n) (e : Fin m ↪ Fin n)
    {I : Finset (Fin m)} (h : ShortZero (pullSeq S e) I) :
    ShortZero S (I.map e) := by sorry
