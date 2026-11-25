-- Prove2me | Theorems.Thm_KneserColouring_pref_le
-- name    : KneserColouring.pref_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:54.531826+00:00
-- url     : https://prove2.me/theorems/21eb7623-a420-4d8a-81e2-3148f316ca58
-- title:
--   Kneser Colouring: pref le
-- statement:
--   The Kneser Colouring construction uses the pref le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L109-L116
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L109-L116

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

theorem KneserColouring.pref_le (r : Room n) {i j : ℕ} (hij : i ≤ j) :
    ∀ c, pref r i c ≠ 0 → pref r i c = pref r j c := by sorry
