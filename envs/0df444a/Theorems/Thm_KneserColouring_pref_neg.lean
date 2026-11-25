-- Prove2me | Theorems.Thm_KneserColouring_pref_neg
-- name    : KneserColouring.pref_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:47.532973+00:00
-- url     : https://prove2.me/theorems/c0a49cee-00be-5d48-8778-4d5575697075
-- title:
--   Kneser Colouring: pref neg
-- statement:
--   The Kneser Colouring construction uses the pref neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L140-L143
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L140-L143

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

theorem KneserColouring.pref_neg (r : Room n) (i : ℕ) : pref (-r.1, r.2) i = -pref r i := by sorry
