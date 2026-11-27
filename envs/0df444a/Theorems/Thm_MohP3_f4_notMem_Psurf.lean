-- Prove2me | Theorems.Thm_MohP3_f4_notMem_Psurf
-- name    : MohP3.f4_notMem_Psurf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:05:14.904618+00:00
-- url     : https://prove2.me/theorems/a70414a7-7569-451a-af9a-8074548ce6a7
-- title:
--   Moh P3: f4 not Mem Psurf
-- statement:
--   `f4` vanishes on the curve but not on the surface.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L114-L121
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L114-L121

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

theorem MohP3.f4_notMem_Psurf : f4 ∉ Psurf := by sorry
