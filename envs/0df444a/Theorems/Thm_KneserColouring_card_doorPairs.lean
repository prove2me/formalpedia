-- Prove2me | Theorems.Thm_KneserColouring_card_doorPairs
-- name    : KneserColouring.card_doorPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:14.582804+00:00
-- url     : https://prove2.me/theorems/4587e9fd-9db2-58b4-90a2-e30a4f8cf4cb
-- title:
--   Kneser Colouring: card door Pairs
-- statement:
--   The Kneser Colouring construction uses the card door Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L60-L67
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L60-L67

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

theorem KneserColouring.card_doorPairs (lab : (Fin n → SignType) → ℤ) (K : ℕ) :
    (doorPairs lab K).card =
      ∑ r ∈ univ.filter (fun r : Room n => IsUpper K r),
        ((range K).filter (door lab K r)).card := by sorry
