-- Prove2me | Theorems.Thm_MohP3_Psurf_le_P
-- name    : MohP3.Psurf_le_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:04:33.970663+00:00
-- url     : https://prove2.me/theorems/713069dc-6a12-501c-b15c-ddb31f8d84a3
-- title:
--   Moh P3: Psurf le P
-- statement:
--   Every polynomial vanishing on the surface vanishes on the Moh curve.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L93-L97
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L93-L97

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

theorem MohP3.Psurf_le_P : Psurf ≤ P := by sorry
