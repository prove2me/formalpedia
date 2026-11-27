-- Prove2me | Theorems.Thm_MohP3_FormalLocal_iter_wOrd
-- name    : MohP3.FormalLocal.iter_wOrd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:37.649994+00:00
-- url     : https://prove2.me/theorems/74fcbee7-28ec-418a-9528-1b7fc19c0ca1
-- title:
--   Formal Local: iter w Ord
-- statement:
--   The Formal Local construction uses the iter w Ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L475-L478
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L475-L478

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.FormalLocal.iter_wOrd (F : Sk k) (s : ℕ) : WOrd (iter k F s).1 s := by sorry
