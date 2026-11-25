-- Prove2me | Theorems.Thm_KneserColouring_IsRoom_perm_lt
-- name    : KneserColouring.IsRoom.perm_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:33.085704+00:00
-- url     : https://prove2.me/theorems/9a308e2c-922e-5afa-b84b-c07774ff17f0
-- title:
--   Is Room: perm lt
-- statement:
--   The Is Room construction uses the perm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L81-L87
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L81-L87

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

theorem KneserColouring.IsRoom.perm_lt {k : ℕ} {r : Room n} (h : IsRoom k r) {c : Fin n} (hc : c.val < k) :
    (r.2 c).val < k := by sorry
