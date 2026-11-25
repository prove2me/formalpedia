-- Prove2me | Theorems.Thm_HiltonMilner_wt_shift_lt
-- name    : HiltonMilner.wt_shift_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:58.040726+00:00
-- url     : https://prove2.me/theorems/51103f0c-728a-4d10-9940-e24c3454adf8
-- title:
--   Hilton Milner: wt shift lt
-- statement:
--   The Hilton Milner construction uses the wt shift lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L155-L160
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L155-L160

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.wt_shift_lt {y z : ℕ} (hyz : y < z) {A : Finset ℕ} (hyA : y ∉ A) (hzA : z ∈ A) :
    wt (insert y (A.erase z)) < wt A := by sorry
