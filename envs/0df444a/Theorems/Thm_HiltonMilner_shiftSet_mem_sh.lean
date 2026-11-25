-- Prove2me | Theorems.Thm_HiltonMilner_shiftSet_mem_sh
-- name    : HiltonMilner.shiftSet_mem_sh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:47.653804+00:00
-- url     : https://prove2.me/theorems/d084e9b1-56f5-4556-8904-27de35557d53
-- title:
--   Hilton Milner: shift Set mem sh
-- statement:
--   The Hilton Milner construction uses the shift Set mem sh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L74-L76
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L74-L76

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.shiftSet_mem_sh {y z : ℕ} {𝒜 : Finset (Finset ℕ)} {A : Finset ℕ} (hA : A ∈ 𝒜) :
    shiftSet y z A ∈ sh y z 𝒜 := by sorry
