-- Prove2me | Theorems.Thm_KneserColouring_exists_maxCol
-- name    : KneserColouring.exists_maxCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:21.05924+00:00
-- url     : https://prove2.me/theorems/65fbd194-9589-494f-a628-4e7886707dc4
-- title:
--   Kneser Colouring: exists max Col
-- statement:
--   The Kneser Colouring construction uses the exists max Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L125-L136
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L125-L136

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

theorem KneserColouring.exists_maxCol (c : {s : Finset (Fin n) // s.card = k} → Fin q) {B : Finset (Fin n)}
    (h : 1 ≤ maxCol c B) :
    ∃ A, ∃ hA : A.card = k, A ⊆ B ∧ (c ⟨A, hA⟩).val + 1 = maxCol c B := by sorry
