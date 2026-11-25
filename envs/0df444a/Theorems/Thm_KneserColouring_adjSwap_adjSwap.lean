-- Prove2me | Theorems.Thm_KneserColouring_adjSwap_adjSwap
-- name    : KneserColouring.adjSwap_adjSwap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:02.525278+00:00
-- url     : https://prove2.me/theorems/a93cd3dd-b37f-5e5f-99a0-e7f5ba481063
-- title:
--   Kneser Colouring: adj Swap adj Swap
-- statement:
--   The Kneser Colouring construction uses the adj Swap adj Swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L154-L158
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L154-L158

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}

theorem KneserColouring.adjSwap_adjSwap (j : ℕ) (c : Fin n) : adjSwap n j (adjSwap n j c) = c := by sorry
