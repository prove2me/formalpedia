-- Prove2me | Theorems.Thm_MohP3_FormalLocal_Psurfk_isPrime
-- name    : MohP3.FormalLocal.Psurfk_isPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:47.526517+00:00
-- url     : https://prove2.me/theorems/e7f21f60-ab14-4d2b-bed5-cfb3fc62916e
-- title:
--   Formal Local: Psurfk is Prime
-- statement:
--   The Formal Local construction uses the Psurfk is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L146-L146
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L146-L146

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

theorem MohP3.FormalLocal.Psurfk_isPrime : (Psurfk k).IsPrime := by sorry
