-- Prove2me | Theorems.Thm_KneserColouring_even_card_swapPairs
-- name    : KneserColouring.even_card_swapPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:48.577287+00:00
-- url     : https://prove2.me/theorems/dced2408-148c-47df-b902-93b1f33e1857
-- title:
--   Kneser Colouring: even card swap Pairs
-- statement:
--   The Kneser Colouring construction uses the even card swap Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L98-L140
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L98-L140

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}

theorem KneserColouring.even_card_swapPairs (lab : (Fin n → SignType) → ℤ) {k : ℕ} (hkn : k + 1 ≤ n) :
    Even ((doorPairs lab (k + 1)).filter (fun p => p.2 < k)).card := by sorry
