-- Prove2me | Theorems.Thm_HiltonMilner_hilton_milner
-- name    : HiltonMilner.hilton_milner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:05:44.926511+00:00
-- url     : https://prove2.me/theorems/3e5c73ad-ab84-4e0c-b558-41c98c995b51
-- title:
--   Hilton Milner: hilton milner
-- statement:
--   **Hilton–Milner (1967).**
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HiltonMilner.lean#L55-L81
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HiltonMilner.lean#L55-L81

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HMCore
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.hilton_milner {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k < n) {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) (hs : (𝒜 : Set (Finset (Fin n))).Sized k)
    (hnt : ∀ x : Fin n, ∃ A ∈ 𝒜, x ∉ A) :
    #𝒜 ≤ (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1 := by sorry
