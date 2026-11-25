-- Prove2me | Theorems.Thm_HiltonMilnerTheorem_exists_hiltonMilner_family
-- name    : HiltonMilnerTheorem.exists_hiltonMilner_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:29:33.78264+00:00
-- url     : https://prove2.me/theorems/6266bbb7-fd55-55ac-934d-7c45af9157b0
-- title:
--   Hilton Milner Theorem: exists hilton Milner family
-- statement:
--   The Hilton–Milner bound is attained.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/Solution.lean#L38-L42
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/Solution.lean#L38-L42

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
public import Definitions.Def_HiltonMilner_Solution
public import Theorems.Thm_HiltonMilner_exists_hiltonMilner_family

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilnerTheorem

theorem HiltonMilnerTheorem.exists_hiltonMilner_family {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k < n) :
    ∃ 𝒜 : Finset (Finset (Fin n)), (𝒜 : Set (Finset (Fin n))).Intersecting ∧
      (𝒜 : Set (Finset (Fin n))).Sized k ∧ (∀ x : Fin n, ∃ A ∈ 𝒜, x ∉ A) ∧
      #𝒜 = (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1 := by sorry
