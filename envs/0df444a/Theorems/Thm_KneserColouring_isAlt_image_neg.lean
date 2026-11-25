-- Prove2me | Theorems.Thm_KneserColouring_isAlt_image_neg
-- name    : KneserColouring.isAlt_image_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:18.818918+00:00
-- url     : https://prove2.me/theorems/e491f42d-3d1a-45c5-a245-07f4b17e890b
-- title:
--   Kneser Colouring: is Alt image neg
-- statement:
--   The Kneser Colouring construction uses the is Alt image neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L274-L298
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L274-L298

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.isAlt_image_neg {s : ℕ} {S : Finset ℤ} (h0 : (0 : ℤ) ∉ S) :
    IsAlt s (S.image (fun a => -a)) ↔ IsAlt (s + 1) S := by sorry
