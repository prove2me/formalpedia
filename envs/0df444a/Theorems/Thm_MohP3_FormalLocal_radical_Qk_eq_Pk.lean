-- Prove2me | Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_Pk
-- name    : MohP3.FormalLocal.radical_Qk_eq_Pk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:23.292785+00:00
-- url     : https://prove2.me/theorems/df179c5b-d324-4bba-9d05-b6bf1605c6a9
-- title:
--   Formal Local: radical Qk eq Pk
-- statement:
--   The formal-local theorem, in the form `(Qk).radical = Pk`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L43-L44
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L43-L44

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

theorem MohP3.FormalLocal.radical_Qk_eq_Pk : (Qk k).radical = Pk k := by sorry
