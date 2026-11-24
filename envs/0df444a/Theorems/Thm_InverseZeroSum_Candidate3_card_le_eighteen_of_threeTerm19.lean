-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_card_le_eighteen_of_threeTerm19
-- name    : InverseZeroSum.Candidate3.card_le_eighteen_of_threeTerm19
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:17.509131+00:00
-- url     : https://prove2.me/theorems/af98e599-825f-4084-90c4-dcfbf1ec552e
-- title:
--   Candidate3: card le eighteen of three Term19
-- statement:
--   The published three-term length-19 source interface bounds a set of positions
--   with no three-term zero sum by 18.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1045-L1067
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L1045-L1067

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.card_le_eighteen_of_threeTerm19 (h19 : ThreeTerm19Input)
    (S : PosSeq 24) {A : Finset (Fin 24)}
    (hNoThree :
      ∀ I : Finset (Fin 24), I ⊆ A → I.card = 3 → posSum S I ≠ 0) :
    A.card ≤ 18 := by sorry
