-- Prove2me | Theorems.Thm_MohP3_sigma_z
-- name    : MohP3.sigma_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:23.891612+00:00
-- url     : https://prove2.me/theorems/b528607c-574c-52a6-bdf6-4f114c319d6d
-- title:
--   Moh P3: sigma z
-- statement:
--   The Moh P3 construction uses the sigma z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L82-L83
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L82-L83

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

theorem MohP3.sigma_z : sigma z = (X 1 : Rsurf)^5 := by sorry
