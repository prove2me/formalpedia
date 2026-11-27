-- Prove2me | Theorems.Thm_MohP3_FormalLocal_Pk_isPrime
-- name    : MohP3.FormalLocal.Pk_isPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:44.690833+00:00
-- url     : https://prove2.me/theorems/00244ab7-d4fe-5bcb-917c-169b1835a167
-- title:
--   Formal Local: Pk is Prime
-- statement:
--   The Formal Local construction uses the Pk is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L40-L40
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L40-L40

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

theorem MohP3.FormalLocal.Pk_isPrime : (Pk k).IsPrime := by sorry
