-- Prove2me | Theorems.Thm_MohP3_FormalLocal_exp8_ne_zero
-- name    : MohP3.FormalLocal.exp8_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:58:05.946263+00:00
-- url     : https://prove2.me/theorems/0ec0cf85-a68b-49b6-b6b2-70929d8c98c5
-- title:
--   Formal Local: exp8 ne zero
-- statement:
--   The Formal Local construction uses the exp8 ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L232-L236
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L232-L236

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

theorem MohP3.FormalLocal.exp8_ne_zero {q : PowerSeries k} (hq : q ≠ 0) : exp8 k q ≠ 0 := by sorry
