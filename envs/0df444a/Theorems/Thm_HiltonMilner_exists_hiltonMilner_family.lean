-- Prove2me | Theorems.Thm_HiltonMilner_exists_hiltonMilner_family
-- name    : HiltonMilner.exists_hiltonMilner_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:05:04.267519+00:00
-- url     : https://prove2.me/theorems/67f40bb4-e63c-56b7-9796-17028edff2aa
-- title:
--   Hilton Milner: exists hilton Milner family
-- statement:
--   The Hilton–Milner bound is attained.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HiltonMilner.lean#L84-L171
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HiltonMilner.lean#L84-L171

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.exists_hiltonMilner_family {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k < n) :
    ∃ 𝒜 : Finset (Finset (Fin n)), (𝒜 : Set (Finset (Fin n))).Intersecting ∧
      (𝒜 : Set (Finset (Fin n))).Sized k ∧ (∀ x : Fin n, ∃ A ∈ 𝒜, x ∉ A) ∧
      #𝒜 = (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1 := by sorry
