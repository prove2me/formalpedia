-- Prove2me | Theorems.Thm_KneserColouring_negPart_neg
-- name    : KneserColouring.negPart_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:08.951984+00:00
-- url     : https://prove2.me/theorems/4dc0cca5-d144-537a-b8e0-89bd0eca14c5
-- title:
--   Kneser Colouring: neg Part neg
-- statement:
--   The Kneser Colouring construction uses the neg Part neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L161-L164
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L161-L164

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}

theorem KneserColouring.negPart_neg (x : Fin n → SignType) : negPart (-x) = posPart x := by sorry
