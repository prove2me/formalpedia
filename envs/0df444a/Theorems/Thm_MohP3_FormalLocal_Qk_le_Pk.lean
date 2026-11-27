-- Prove2me | Theorems.Thm_MohP3_FormalLocal_Qk_le_Pk
-- name    : MohP3.FormalLocal.Qk_le_Pk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:18:08.7034+00:00
-- url     : https://prove2.me/theorems/19c945c6-e31b-5c99-bde8-6022f192dadd
-- title:
--   Formal Local: Qk le Pk
-- statement:
--   The Formal Local construction uses the Qk le Pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L111-L111
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L111-L111

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
omit [CharZero k]

theorem MohP3.FormalLocal.Qk_le_Pk : Qk k ≤ Pk k := by sorry
