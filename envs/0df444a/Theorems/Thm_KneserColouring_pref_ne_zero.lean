-- Prove2me | Theorems.Thm_KneserColouring_pref_ne_zero
-- name    : KneserColouring.pref_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:28.357294+00:00
-- url     : https://prove2.me/theorems/4c43cd2c-d593-56a2-a9fc-98779a4fb023
-- title:
--   Kneser Colouring: pref ne zero
-- statement:
--   The Kneser Colouring construction uses the pref ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L100-L107
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L100-L107

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

theorem KneserColouring.pref_ne_zero {k : ℕ} {r : Room n} (h : IsRoom k r) (hk : k ≤ n) {i : ℕ} (hi : i < k) :
    pref r (i + 1) ≠ 0 := by sorry
