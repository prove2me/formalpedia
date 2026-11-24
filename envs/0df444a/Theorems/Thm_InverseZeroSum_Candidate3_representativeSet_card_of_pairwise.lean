-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_representativeSet_card_of_pairwise
-- name    : InverseZeroSum.Candidate3.representativeSet_card_of_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:22:53.5678+00:00
-- url     : https://prove2.me/theorems/0101ff8f-7944-46be-9628-313c5880e087
-- title:
--   Candidate3: representative Set card of pairwise
-- statement:
--   One chosen representative from each pairwise-disjoint block gives exactly as
--   many deleted positions as there are blocks.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L309-L324
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L309-L324

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.representativeSet_card_of_pairwise {s : ℕ}
    {blocks : Fin s → Finset (Fin 24)} {rep : Fin s → Fin 24}
    (hBlocks : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hRep : ∀ j, rep j ∈ blocks j) :
    (representativeSet rep).card = s := by sorry
