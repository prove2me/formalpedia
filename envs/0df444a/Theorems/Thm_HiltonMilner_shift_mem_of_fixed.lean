-- Prove2me | Theorems.Thm_HiltonMilner_shift_mem_of_fixed
-- name    : HiltonMilner.shift_mem_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:29.172846+00:00
-- url     : https://prove2.me/theorems/981007cc-87fb-444e-a4cc-2a53a32fa3e0
-- title:
--   Hilton Milner: shift mem of fixed
-- statement:
--   In a family fixed by the shift, the shift of a member is a member.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L193-L198
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L193-L198

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.shift_mem_of_fixed {y z : ℕ} {𝒜 : Finset (Finset ℕ)} (hfix : sh y z 𝒜 = 𝒜) {A : Finset ℕ}
    (hA : A ∈ 𝒜) (hyA : y ∉ A) (hzA : z ∈ A) : insert y (A.erase z) ∈ 𝒜 := by sorry
