-- Prove2me | Theorems.Thm_KneserColouring_count_isAlt_erase
-- name    : KneserColouring.count_isAlt_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:01.022566+00:00
-- url     : https://prove2.me/theorems/46b52a11-2ae0-5c12-a2cb-cf056f2e074b
-- title:
--   Kneser Colouring: count is Alt erase
-- statement:
--   The key parity count: for a nonempty set `S` without opposite elements, the number of
--   `a ∈ S` such that `S \ {a}` is positively alternating is odd iff `S` is alternating.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L92-L177
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L92-L177

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.count_isAlt_erase (S : Finset ℤ) (hS : NoComp S) (hne : S.Nonempty) :
    (S.filter (fun a => IsAlt 0 (S.erase a))).card % 2 = 1 ↔ (IsAlt 0 S ∨ IsAlt 1 S) := by sorry
