-- Prove2me | Theorems.Thm_KneserColouring_signType_neg_ne_self
-- name    : KneserColouring.signType_neg_ne_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:13.363665+00:00
-- url     : https://prove2.me/theorems/a76b9a3d-15ca-532f-9e84-16700df8ee73
-- title:
--   Kneser Colouring: sign Type neg ne self
-- statement:
--   The Kneser Colouring construction uses the sign Type neg ne self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L43-L44
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L43-L44

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

theorem KneserColouring.signType_neg_ne_self {s : SignType} (h : s ≠ 0) : -s ≠ s := by sorry
