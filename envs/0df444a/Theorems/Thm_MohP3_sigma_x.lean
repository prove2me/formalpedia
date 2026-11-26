-- Prove2me | Theorems.Thm_MohP3_sigma_x
-- name    : MohP3.sigma_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:44.379689+00:00
-- url     : https://prove2.me/theorems/a437b768-583c-48f6-9d62-1756cb9d57e9
-- title:
--   Moh P3: sigma x
-- statement:
--   The Moh P3 construction uses the sigma x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L77-L77
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L77-L77

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

theorem MohP3.sigma_x : sigma x = X 0 := by sorry
