-- Prove2me | Theorems.Thm_KneserColouring_NoComp_ne_zero
-- name    : KneserColouring.NoComp.ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:02.31373+00:00
-- url     : https://prove2.me/theorems/f9b3cadf-3a25-5291-b937-854608f6cbe0
-- title:
--   No Comp: ne zero
-- statement:
--   The No Comp construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L55-L56
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L55-L56

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.NoComp.ne_zero {S : Finset ℤ} (h : NoComp S) {a : ℤ} (ha : a ∈ S) : a ≠ 0 := by sorry
