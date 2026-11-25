-- Prove2me | Theorems.Thm_HiltonMilner_Cross_mono
-- name    : HiltonMilner.Cross.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:34.232932+00:00
-- url     : https://prove2.me/theorems/08ee0ba1-2c64-4c4e-947f-1bab0839e41e
-- title:
--   Cross: mono
-- statement:
--   The Cross construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L33-L35
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L33-L35

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.Cross.mono {𝒜 ℬ 𝒜' ℬ' : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ) (h𝒜 : 𝒜' ⊆ 𝒜)
    (hℬ : ℬ' ⊆ ℬ) : Cross 𝒜' ℬ' := by sorry
