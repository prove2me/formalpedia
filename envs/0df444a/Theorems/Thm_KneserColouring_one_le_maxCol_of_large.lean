-- Prove2me | Theorems.Thm_KneserColouring_one_le_maxCol_of_large
-- name    : KneserColouring.one_le_maxCol_of_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:52.196179+00:00
-- url     : https://prove2.me/theorems/41fbe37f-8a40-4aa3-9074-1928686d41ae
-- title:
--   Kneser Colouring: one le max Col of large
-- statement:
--   The Kneser Colouring construction uses the one le max Col of large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L191-L197
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L191-L197

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

theorem KneserColouring.one_le_maxCol_of_large (c : {s : Finset (Fin n) // s.card = k} → Fin q) (hk : 0 < k)
    {x : Fin n → SignType} (hx : ¬ suppCard x ≤ 2 * k - 2) :
    1 ≤ maxCol c (posPart x) ∨ 1 ≤ maxCol c (negPart x) := by sorry
