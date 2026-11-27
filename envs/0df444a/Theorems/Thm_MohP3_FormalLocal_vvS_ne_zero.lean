-- Prove2me | Theorems.Thm_MohP3_FormalLocal_vvS_ne_zero
-- name    : MohP3.FormalLocal.vvS_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:56.104429+00:00
-- url     : https://prove2.me/theorems/798f7afa-4406-543d-a431-9cc7b16cfc56
-- title:
--   Formal Local: vv S ne zero
-- statement:
--   The Formal Local construction uses the vv S ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L213-L217
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L213-L217

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

theorem MohP3.FormalLocal.vvS_ne_zero (i : Fin 8) : vvS k i ≠ 0 := by sorry
