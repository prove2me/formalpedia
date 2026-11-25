-- Prove2me | Theorems.Thm_KneserColouring_card_boundaryPairs
-- name    : KneserColouring.card_boundaryPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:57.644547+00:00
-- url     : https://prove2.me/theorems/108a5cfb-1837-4f8c-8040-a34e7511eaae
-- title:
--   Kneser Colouring: card boundary Pairs
-- statement:
--   The Kneser Colouring construction uses the card boundary Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L216-L307
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L216-L307

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}

theorem KneserColouring.card_boundaryPairs (lab : (Fin n → SignType) → ℤ) {k : ℕ} (hkn : k + 1 ≤ n) :
    (((doorPairs lab (k + 1)).filter (fun p => ¬ p.2 < k)).filter
      (fun p => ¬ p.1.2 ⟨k, by omega⟩ ≠ ⟨k, by omega⟩)).card =
    (univ.filter (fun r : Room n => IsRoom k r ∧ IsAlt 0 (labSet lab k r) ∧
      (labSet lab k r).card = k)).card := by sorry
