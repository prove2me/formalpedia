-- Prove2me | Theorems.Thm_MohP3_FormalLocal_psi_eq_tauS_sigmaS
-- name    : MohP3.FormalLocal.psi_eq_tauS_sigmaS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:52.081267+00:00
-- url     : https://prove2.me/theorems/69e9574c-b066-5c5f-8f38-7b3e05040bd8
-- title:
--   Formal Local: psi eq tau S sigma S
-- statement:
--   The Moh curve lies on the surface `y^5 = z^4`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L129-L135
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L129-L135

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.FormalLocal.psi_eq_tauS_sigmaS (f : Sk k) : psi k f = tauS k (sigmaS k f) := by sorry
