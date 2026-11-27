-- Prove2me | Theorems.Thm_MohP3_FormalLocal_chiS_X0
-- name    : MohP3.FormalLocal.chiS_X0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:37.546222+00:00
-- url     : https://prove2.me/theorems/84ca1e1b-1eb0-5e84-a0da-40cfb3d165e1
-- title:
--   Formal Local: chi S X0
-- statement:
--   The Formal Local construction uses the chi S X0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L192-L193
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L192-L193

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

theorem MohP3.FormalLocal.chiS_X0 : chiS k (X 0) = PowerSeries.X := by sorry
