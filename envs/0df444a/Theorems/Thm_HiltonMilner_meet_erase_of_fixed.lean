-- Prove2me | Theorems.Thm_HiltonMilner_meet_erase_of_fixed
-- name    : HiltonMilner.meet_erase_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:50:11.683903+00:00
-- url     : https://prove2.me/theorems/68793386-9411-4ab4-801f-140741b87865
-- title:
--   Hilton Milner: meet erase of fixed
-- statement:
--   In two families fixed by all shifts into the top element `z`, two members through `z` meet
--   outside `z`, provided their union is not the whole ground set.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L202-L219
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L202-L219

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.meet_erase_of_fixed {X : Finset ℕ} {z : ℕ} {𝒜 ℬ : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ)
    (hfix : ∀ y ∈ X.erase z, sh y z ℬ = ℬ) {A B : Finset ℕ} (hA : A ∈ 𝒜) (hB : B ∈ ℬ)
    (hzA : z ∈ A) (hzB : z ∈ B) (hcard : #(A ∪ B) < #X) :
    (A.erase z ∩ B.erase z).Nonempty := by sorry
