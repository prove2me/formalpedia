-- Prove2me | Theorems.Thm_KneserColouring_one_le_suppCard
-- name    : KneserColouring.one_le_suppCard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:25.042867+00:00
-- url     : https://prove2.me/theorems/b929074d-a4f3-5c9d-8c32-022c10ccc03f
-- title:
--   Kneser Colouring: one le supp Card
-- statement:
--   The Kneser Colouring construction uses the one le supp Card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L187-L189
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L187-L189

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

theorem KneserColouring.one_le_suppCard {x : Fin n → SignType} (hx : x ≠ 0) : 1 ≤ suppCard x := by sorry
