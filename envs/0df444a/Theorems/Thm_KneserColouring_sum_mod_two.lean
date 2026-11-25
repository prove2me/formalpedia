-- Prove2me | Theorems.Thm_KneserColouring_sum_mod_two
-- name    : KneserColouring.sum_mod_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:19.522453+00:00
-- url     : https://prove2.me/theorems/f885a7a8-647c-454b-b8f5-3651b9eab653
-- title:
--   Kneser Colouring: sum mod two
-- statement:
--   The Kneser Colouring construction uses the sum mod two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L28-L38
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L28-L38

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

theorem KneserColouring.sum_mod_two {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) % 2 = (s.filter (fun x => f x % 2 = 1)).card % 2 := by sorry
