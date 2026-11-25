-- Prove2me | Theorems.Thm_KneserColouring_even_card_flipPairs
-- name    : KneserColouring.even_card_flipPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:36.231009+00:00
-- url     : https://prove2.me/theorems/28960d34-40ae-5b51-b226-f03bbd4a06df
-- title:
--   Kneser Colouring: even card flip Pairs
-- statement:
--   The Kneser Colouring construction uses the even card flip Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L142-L214
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L142-L214

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

theorem KneserColouring.even_card_flipPairs (lab : (Fin n → SignType) → ℤ) {k : ℕ} (hkn : k + 1 ≤ n) :
    Even (((doorPairs lab (k + 1)).filter (fun p => ¬ p.2 < k)).filter
      (fun p => p.1.2 ⟨k, by omega⟩ ≠ ⟨k, by omega⟩)).card := by sorry
