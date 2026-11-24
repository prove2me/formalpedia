-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_posSum_representativeSet_eq_sum
-- name    : InverseZeroSum.Candidate3.posSum_representativeSet_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:30:15.510893+00:00
-- url     : https://prove2.me/theorems/acf5047a-838a-4f17-8766-3ecf92b5bebc
-- title:
--   Candidate3: pos Sum representative Set eq sum
-- statement:
--   The sum over a representative position set is the sum over block indices.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2047-L2065
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2047-L2065

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.posSum_representativeSet_eq_sum {s : ℕ} (S : PosSeq 24)
    {blocks : Fin s → Finset (Fin 24)} {rep : Fin s → Fin 24}
    (hBlocks : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hRep : ∀ j, rep j ∈ blocks j) :
    posSum S (representativeSet rep) =
      ∑ j : Fin s, (S (rep j) : G) := by sorry
