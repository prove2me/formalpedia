-- Prove2me | Theorems.Thm_KneserColouring_signType_neg_ne_zero
-- name    : KneserColouring.signType_neg_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:05.836771+00:00
-- url     : https://prove2.me/theorems/104e4085-a953-54c0-aa45-248cf5ac7c07
-- title:
--   Kneser Colouring: sign Type neg ne zero
-- statement:
--   The Kneser Colouring construction uses the sign Type neg ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L40-L41
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L40-L41

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

theorem KneserColouring.signType_neg_ne_zero (s : SignType) : -s ≠ 0 ↔ s ≠ 0 := by sorry
