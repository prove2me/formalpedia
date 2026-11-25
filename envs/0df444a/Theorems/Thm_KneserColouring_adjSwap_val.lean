-- Prove2me | Theorems.Thm_KneserColouring_adjSwap_val
-- name    : KneserColouring.adjSwap_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:11.173745+00:00
-- url     : https://prove2.me/theorems/415e5cca-d7c0-43f2-bd9c-970753231875
-- title:
--   Kneser Colouring: adj Swap val
-- statement:
--   The Kneser Colouring construction uses the adj Swap val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L149-L152
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L149-L152

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}

theorem KneserColouring.adjSwap_val {j : ℕ} (h : j + 1 < n) (c : Fin n) :
    (adjSwap n j c).val = if c.val = j then j + 1 else if c.val = j + 1 then j else c.val := by sorry
