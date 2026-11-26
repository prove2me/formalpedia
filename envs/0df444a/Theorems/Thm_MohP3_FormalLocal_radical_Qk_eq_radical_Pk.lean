-- Prove2me | Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_radical_Pk
-- name    : MohP3.FormalLocal.radical_Qk_eq_radical_Pk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:53:40.056304+00:00
-- url     : https://prove2.me/theorems/ae814522-8586-4e9a-afdb-9e14e5c20506
-- title:
--   Formal Local: radical Qk eq radical Pk
-- statement:
--   The Formal Local construction uses the radical Qk eq radical Pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L115-L116
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L115-L116

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.FormalLocal.radical_Qk_eq_radical_Pk : (Qk k).radical = (Pk k).radical := by sorry
