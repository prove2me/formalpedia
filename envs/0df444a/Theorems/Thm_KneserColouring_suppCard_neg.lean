-- Prove2me | Theorems.Thm_KneserColouring_suppCard_neg
-- name    : KneserColouring.suppCard_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:04.934428+00:00
-- url     : https://prove2.me/theorems/7b8ab123-4dc1-5ff3-a0b7-af9a4cac2921
-- title:
--   Kneser Colouring: supp Card neg
-- statement:
--   The Kneser Colouring construction uses the supp Card neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L166-L171
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L166-L171

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

theorem KneserColouring.suppCard_neg (x : Fin n → SignType) : suppCard (-x) = suppCard x := by sorry
