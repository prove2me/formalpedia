-- Prove2me | Theorems.Thm_KneserColouring_altCount_succ
-- name    : KneserColouring.altCount_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:35.818436+00:00
-- url     : https://prove2.me/theorems/045babf0-4723-514f-8cf4-480e53cdbf26
-- title:
--   Kneser Colouring: alt Count succ
-- statement:
--   The Kneser Colouring construction uses the alt Count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L126-L138
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L126-L138

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

theorem KneserColouring.altCount_succ (lab : (Fin n → SignType) → ℤ) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    (hNC : NoCompLab lab) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) :
    altCount lab (k + 1) % 2 = altCount lab k % 2 := by sorry
