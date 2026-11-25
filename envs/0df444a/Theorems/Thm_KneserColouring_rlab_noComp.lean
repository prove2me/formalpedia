-- Prove2me | Theorems.Thm_KneserColouring_rlab_noComp
-- name    : KneserColouring.rlab_noComp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:50.994804+00:00
-- url     : https://prove2.me/theorems/6cb0b800-4770-45d2-b672-77c4d6e2bcbf
-- title:
--   Kneser Colouring: rlab no Comp
-- statement:
--   The Kneser Colouring construction uses the rlab no Comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L118-L130
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L118-L130

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

theorem KneserColouring.rlab_noComp {lab : (Fin n → SignType) → ℤ} (hNC : NoCompLab lab) {k : ℕ} {r : Room n}
    (h : IsRoom k r) (hk : k ≤ n) :
    ∀ i ∈ range k, ∀ j ∈ range k, rlab lab r i ≠ -rlab lab r j := by sorry
