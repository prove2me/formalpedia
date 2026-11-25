-- Prove2me | Theorems.Thm_HiltonMilner_lt_max_of_mem_erase
-- name    : HiltonMilner.lt_max_of_mem_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:59:05.273953+00:00
-- url     : https://prove2.me/theorems/3e63c382-d726-4095-90e4-d511c5c7ecbe
-- title:
--   Hilton Milner: lt max of mem erase
-- statement:
--   Shifts into the top element of the ground set decrease the weight.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L98-L100
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L98-L100

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.lt_max_of_mem_erase {X : Finset ℕ} (hX : X.Nonempty) {y : ℕ} (hy : y ∈ X.erase (X.max' hX)) :
    y < X.max' hX := by sorry
