-- Prove2me | Theorems.Thm_KneserColouring_maxCol_ne_of_disjoint
-- name    : KneserColouring.maxCol_ne_of_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:44.377843+00:00
-- url     : https://prove2.me/theorems/5ed2065e-f7a9-5556-b8fb-e1decd386b31
-- title:
--   Kneser Colouring: max Col ne of disjoint
-- statement:
--   The Kneser Colouring construction uses the max Col ne of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L138-L154
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L138-L154

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

theorem KneserColouring.maxCol_ne_of_disjoint (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    (hc : ∀ s t, s ≠ t → Disjoint s.1 t.1 → c s ≠ c t) (hk : 0 < k)
    {B1 B2 : Finset (Fin n)} (hd : Disjoint B1 B2) (h1 : 1 ≤ maxCol c B1)
    (heq : maxCol c B1 = maxCol c B2) : False := by sorry
