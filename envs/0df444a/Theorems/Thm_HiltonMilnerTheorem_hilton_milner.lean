-- Prove2me | Theorems.Thm_HiltonMilnerTheorem_hilton_milner
-- name    : HiltonMilnerTheorem.hilton_milner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:36:09.962446+00:00
-- url     : https://prove2.me/theorems/fd924346-91d6-569d-8fcb-8d9884e8537c
-- title:
--   Hilton Milner Theorem: hilton milner
-- statement:
--   **Hilton–Milner (1967).**
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/Solution.lean#L31-L35
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/Solution.lean#L31-L35

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
public import Definitions.Def_HiltonMilner_Solution
public import Theorems.Thm_HiltonMilner_hilton_milner

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilnerTheorem

theorem HiltonMilnerTheorem.hilton_milner {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k < n) {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) (hs : (𝒜 : Set (Finset (Fin n))).Sized k)
    (hnt : ∀ x : Fin n, ∃ A ∈ 𝒜, x ∉ A) :
    #𝒜 ≤ (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1 := by sorry
