-- Prove2me | Theorems.Thm_KneserColouring_range_succ_erase
-- name    : KneserColouring.range_succ_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:58.423767+00:00
-- url     : https://prove2.me/theorems/c5f1c93e-b0c7-54d4-a11e-88e5eb98b0fb
-- title:
--   Kneser Colouring: range succ erase
-- statement:
--   The Kneser Colouring construction uses the range succ erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L57-L58
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L57-L58

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

theorem KneserColouring.range_succ_erase (k : ℕ) : (range (k + 1)).erase k = range k := by sorry
