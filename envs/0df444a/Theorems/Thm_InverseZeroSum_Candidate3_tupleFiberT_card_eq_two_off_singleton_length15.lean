-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_eq_two_off_singleton_length15
-- name    : InverseZeroSum.Candidate3.tupleFiberT_card_eq_two_off_singleton_length15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:14.525802+00:00
-- url     : https://prove2.me/theorems/24def9af-390a-4eba-b86a-900aa26ea5a1
-- title:
--   Candidate3: tuple Fiber T card eq two off singleton length15
-- statement:
--   Away from the singleton, all seven length-15 support fibres have size two.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2353-L2441
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L2353-L2441

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.tupleFiberT_card_eq_two_off_singleton_length15
    (R : PosSeq 15) (hFree : ShortFree R)
    {u : F3T} (hu : u ∈ tupleSupportT R)
    (huOne :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = u)).card = 1) :
    ∀ x ∈ (tupleSupportT R).erase u,
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = x)).card = 2 := by sorry
