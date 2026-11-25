-- Prove2me | Theorems.Thm_KneserColouring_isRoom_neg
-- name    : KneserColouring.isRoom_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:26.688142+00:00
-- url     : https://prove2.me/theorems/68a98c7c-be06-5b0c-8553-8e37fbea32b1
-- title:
--   Kneser Colouring: is Room neg
-- statement:
--   The Kneser Colouring construction uses the is Room neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L37-L40
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L37-L40

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}

theorem KneserColouring.isRoom_neg {k : ℕ} {t : Fin n → SignType} {ρ : Equiv.Perm (Fin n)} :
    IsRoom k (-t, ρ) ↔ IsRoom k (t, ρ) := by sorry
