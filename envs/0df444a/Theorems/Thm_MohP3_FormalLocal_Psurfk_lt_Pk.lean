-- Prove2me | Theorems.Thm_MohP3_FormalLocal_Psurfk_lt_Pk
-- name    : MohP3.FormalLocal.Psurfk_lt_Pk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:12.035466+00:00
-- url     : https://prove2.me/theorems/70ea4634-5cc9-447d-8d65-2c2799fffd92
-- title:
--   Formal Local: Psurfk lt Pk
-- statement:
--   The Formal Local construction uses the Psurfk lt Pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L214-L216
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L214-L216

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

theorem MohP3.FormalLocal.Psurfk_lt_Pk : Psurfk k < Pk k := by sorry
