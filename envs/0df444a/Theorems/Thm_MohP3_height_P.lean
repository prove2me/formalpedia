-- Prove2me | Theorems.Thm_MohP3_height_P
-- name    : MohP3.height_P
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:06:21.105497+00:00
-- url     : https://prove2.me/theorems/1edfab8c-e98f-42a7-86d1-41d20696a702
-- title:
--   Moh P3: height P
-- statement:
--   **The height of the Moh curve ideal is two.**
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L145-L145
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L145-L145

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.height_P : P.height = 2 := by sorry
