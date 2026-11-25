-- Prove2me | Theorems.Thm_KneserColouring_IsRoom_exists_rank
-- name    : KneserColouring.IsRoom.exists_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:28.64582+00:00
-- url     : https://prove2.me/theorems/47c8c248-b147-5d3a-b205-ae8e2d703be4
-- title:
--   Is Room: exists rank
-- statement:
--   The Is Room construction uses the exists rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L89-L98
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerRooms.lean#L89-L98

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

theorem KneserColouring.IsRoom.exists_rank {k : ℕ} {r : Room n} (h : IsRoom k r) (hk : k ≤ n) {i : ℕ}
    (hi : i < k) : ∃ c : Fin n, c.val < k ∧ (r.2 c).val = i := by sorry
