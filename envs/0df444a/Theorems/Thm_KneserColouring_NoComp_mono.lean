-- Prove2me | Theorems.Thm_KneserColouring_NoComp_mono
-- name    : KneserColouring.NoComp.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:49.547944+00:00
-- url     : https://prove2.me/theorems/975e6c58-74af-587c-a508-cce617cc7e55
-- title:
--   No Comp: mono
-- statement:
--   The No Comp construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L46-L47
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L46-L47

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.NoComp.mono {S T : Finset ℤ} (h : NoComp S) (hT : T ⊆ S) : NoComp T := by sorry
