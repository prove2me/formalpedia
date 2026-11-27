-- Prove2me | Theorems.Thm_MohP3_FormalLocal_height_Pk
-- name    : MohP3.FormalLocal.height_Pk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:56.130739+00:00
-- url     : https://prove2.me/theorems/b522ecae-6338-46cd-8e16-6dd4e013f8e3
-- title:
--   Formal Local: height Pk
-- statement:
--   **After completion the Moh curve ideal still has height two.**
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L237-L238
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L237-L238

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

theorem MohP3.FormalLocal.height_Pk : (Pk k).height = 2 := by sorry
