-- Prove2me | Theorems.Thm_MohP3_FormalLocal_Pk_mem_minimalPrimes_Qk
-- name    : MohP3.FormalLocal.Pk_mem_minimalPrimes_Qk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:10.496173+00:00
-- url     : https://prove2.me/theorems/5e139495-287d-53e5-a98c-b7dc1e5a9af9
-- title:
--   Formal Local: Pk mem minimal Primes Qk
-- statement:
--   The Formal Local construction uses the Pk mem minimal Primes Qk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L46-L47
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L46-L47

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

theorem MohP3.FormalLocal.Pk_mem_minimalPrimes_Qk : Pk k ∈ (Qk k).minimalPrimes := by sorry
