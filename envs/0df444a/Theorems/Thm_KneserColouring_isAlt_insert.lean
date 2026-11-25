-- Prove2me | Theorems.Thm_KneserColouring_isAlt_insert
-- name    : KneserColouring.isAlt_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:12.112006+00:00
-- url     : https://prove2.me/theorems/4eab3afc-79fe-4660-b1d9-d269bd914ab3
-- title:
--   Kneser Colouring: is Alt insert
-- statement:
--   The Kneser Colouring construction uses the is Alt insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L58-L81
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L58-L81

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.isAlt_insert {s : ℕ} {z : ℤ} {T : Finset ℤ} (hz : z ∉ T)
    (hlt : ∀ b ∈ T, |b| < |z|) :
    IsAlt s (insert z T) ↔ IsAlt s T ∧ (0 < z ↔ Even (T.card + s)) := by sorry
