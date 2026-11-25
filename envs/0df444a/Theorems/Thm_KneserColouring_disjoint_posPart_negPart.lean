-- Prove2me | Theorems.Thm_KneserColouring_disjoint_posPart_negPart
-- name    : KneserColouring.disjoint_posPart_negPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:59.012492+00:00
-- url     : https://prove2.me/theorems/a149768a-c649-4d98-971e-0012e9a31ac1
-- title:
--   Kneser Colouring: disjoint pos Part neg Part
-- statement:
--   The Kneser Colouring construction uses the disjoint pos Part neg Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L173-L177
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L173-L177

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}

theorem KneserColouring.disjoint_posPart_negPart (x : Fin n → SignType) : Disjoint (posPart x) (negPart x) := by sorry
