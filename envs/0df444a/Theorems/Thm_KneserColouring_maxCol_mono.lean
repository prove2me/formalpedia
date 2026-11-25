-- Prove2me | Theorems.Thm_KneserColouring_maxCol_mono
-- name    : KneserColouring.maxCol_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:22.627895+00:00
-- url     : https://prove2.me/theorems/40dbdd7d-0833-56ce-8bae-0ce09bc5b1a0
-- title:
--   Kneser Colouring: max Col mono
-- statement:
--   The Kneser Colouring construction uses the max Col mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L114-L116
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L114-L116

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

theorem KneserColouring.maxCol_mono (c : {s : Finset (Fin n) // s.card = k} → Fin q) {B B' : Finset (Fin n)}
    (h : B ⊆ B') : maxCol c B ≤ maxCol c B' := by sorry
