-- Prove2me | Theorems.Thm_KneserColouring_altCount_odd
-- name    : KneserColouring.altCount_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:02.810605+00:00
-- url     : https://prove2.me/theorems/2972ea73-3a03-5241-ac77-7c313e46d5f2
-- title:
--   Kneser Colouring: alt Count odd
-- statement:
--   The Kneser Colouring construction uses the alt Count odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L198-L208
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L198-L208

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

theorem KneserColouring.altCount_odd (lab : (Fin n → SignType) → ℤ) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    (hNC : NoCompLab lab) : ∀ k, 1 ≤ k → k ≤ n → altCount lab k % 2 = 1 := by sorry
