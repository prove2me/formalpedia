-- Prove2me | Theorems.Thm_MohP3_sigma_y
-- name    : MohP3.sigma_y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:06.151801+00:00
-- url     : https://prove2.me/theorems/7ec39da7-0928-4dda-afb9-f8393070aae0
-- title:
--   Moh P3: sigma y
-- statement:
--   The Moh P3 construction uses the sigma y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L79-L80
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L79-L80

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

theorem MohP3.sigma_y : sigma y = (X 1 : Rsurf)^4 := by sorry
