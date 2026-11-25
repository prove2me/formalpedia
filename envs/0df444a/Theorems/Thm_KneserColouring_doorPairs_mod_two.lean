-- Prove2me | Theorems.Thm_KneserColouring_doorPairs_mod_two
-- name    : KneserColouring.doorPairs_mod_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:37.854473+00:00
-- url     : https://prove2.me/theorems/01470296-ff14-4b98-a3b0-eb274550aef0
-- title:
--   Kneser Colouring: door Pairs mod two
-- statement:
--   The Kneser Colouring construction uses the door Pairs mod two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L69-L96
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L69-L96

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

theorem KneserColouring.doorPairs_mod_two (lab : (Fin n → SignType) → ℤ) (hNC : NoCompLab lab) {K : ℕ}
    (hK : 1 ≤ K) (hKn : K ≤ n) :
    (doorPairs lab K).card % 2 = altCount lab K % 2 := by sorry
