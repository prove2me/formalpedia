-- Prove2me | Theorems.Thm_KneserColouring_isAlt_singleton
-- name    : KneserColouring.isAlt_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:54.256141+00:00
-- url     : https://prove2.me/theorems/b1dfe2e8-0622-5bd3-85f4-ea2de6284e15
-- title:
--   Kneser Colouring: is Alt singleton
-- statement:
--   The Kneser Colouring construction uses the is Alt singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L140-L157
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L140-L157

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}

theorem KneserColouring.isAlt_singleton (a : ℤ) : IsAlt 0 {a} ∨ IsAlt 1 {a} := by sorry
