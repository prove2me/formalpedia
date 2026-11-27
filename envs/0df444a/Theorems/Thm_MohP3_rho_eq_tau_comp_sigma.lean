-- Prove2me | Theorems.Thm_MohP3_rho_eq_tau_comp_sigma
-- name    : MohP3.rho_eq_tau_comp_sigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:04:38.083441+00:00
-- url     : https://prove2.me/theorems/599a3878-12a9-5e1d-a9c9-e31a132c92e7
-- title:
--   Moh P3: rho eq tau comp sigma
-- statement:
--   The Moh curve lies on the surface `y^5 = z^4`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L72-L75
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L72-L75

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

theorem MohP3.rho_eq_tau_comp_sigma : rho = tau.comp sigma := by sorry
