-- Prove2me | Theorems.Thm_HiltonMilner_cross_high_low
-- name    : HiltonMilner.cross_high_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:21.681061+00:00
-- url     : https://prove2.me/theorems/929d5844-9177-58d6-bd06-dcea84c0085a
-- title:
--   Hilton Milner: cross high low
-- statement:
--   A member through `z` meets a member avoiding `z` outside `z`.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L81-L89
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L81-L89

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.cross_high_low {z : ℕ} {𝒜 ℬ : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ) :
    Cross (high z 𝒜) (low z ℬ) := by sorry
