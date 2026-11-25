-- Prove2me | Theorems.Thm_KneserColouring_count_doors
-- name    : KneserColouring.count_doors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:26.37996+00:00
-- url     : https://prove2.me/theorems/9175ec1e-299a-4d5f-af11-5be2c266798d
-- title:
--   Kneser Colouring: count doors
-- statement:
--   The parity count for a single room: `ℓ` labels the vertices `s` of a simplex; a facet
--   (`s` minus a vertex `j`) is a *door* when its labels are pairwise distinct and positively
--   alternating. The number of doors is odd iff the labels of `s` are distinct and alternating.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L192-L272
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L192-L272

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.count_doors {α : Type*} [DecidableEq α] (s : Finset α) (ℓ : α → ℤ) (hs : s.Nonempty)
    (hnc : ∀ i ∈ s, ∀ j ∈ s, ℓ i ≠ -ℓ j) :
    (s.filter (fun j => ((s.erase j).image ℓ).card + 1 = s.card ∧
        IsAlt 0 ((s.erase j).image ℓ))).card % 2 = 1 ↔
      ((IsAlt 0 (s.image ℓ) ∨ IsAlt 1 (s.image ℓ)) ∧ (s.image ℓ).card = s.card) := by sorry
