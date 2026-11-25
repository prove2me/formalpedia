-- Prove2me | Theorems.Thm_KneserColouring_NoComp_abs_inj
-- name    : KneserColouring.NoComp.abs_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:05.97389+00:00
-- url     : https://prove2.me/theorems/802cdeed-b9ae-493a-b5a7-a8846a1e673e
-- title:
--   No Comp: abs inj
-- statement:
--   The No Comp construction uses the abs inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L49-L53
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L49-L53

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.NoComp.abs_inj {S : Finset ℤ} (h : NoComp S) {a b : ℤ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : |a| = |b|) : a = b := by sorry
