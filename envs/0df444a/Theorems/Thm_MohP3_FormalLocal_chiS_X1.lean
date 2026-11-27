-- Prove2me | Theorems.Thm_MohP3_FormalLocal_chiS_X1
-- name    : MohP3.FormalLocal.chiS_X1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:08.778791+00:00
-- url     : https://prove2.me/theorems/d520407c-bee4-468c-930b-c17cbdd2d405
-- title:
--   Formal Local: chi S X1
-- statement:
--   The Formal Local construction uses the chi S X1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L196-L197
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L196-L197

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

theorem MohP3.FormalLocal.chiS_X1 : chiS k (X 1) = PowerSeries.X := by sorry
