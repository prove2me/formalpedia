-- Prove2me | Theorems.Thm_KneserColouring_card_sphere
-- name    : KneserColouring.card_sphere
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:34.176333+00:00
-- url     : https://prove2.me/theorems/4df7d3fe-6d84-5ec5-b915-37b3666e42cb
-- title:
--   Kneser Colouring: card sphere
-- statement:
--   The Kneser Colouring construction uses the card sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L48-L124
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L48-L124

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

theorem KneserColouring.card_sphere (lab : (Fin n → SignType) → ℤ) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    (hNC : NoCompLab lab) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (univ.filter (fun r : Room n => IsRoom k r ∧ IsAlt 0 (labSet lab k r) ∧
      (labSet lab k r).card = k)).card = altCount lab k := by sorry
