-- Prove2me | Theorems.Thm_MohP3_FormalLocal_iter_yOrd
-- name    : MohP3.FormalLocal.iter_yOrd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:23.526881+00:00
-- url     : https://prove2.me/theorems/a7adb5b5-3e71-54da-a8ed-52671c1654ce
-- title:
--   Formal Local: iter y Ord
-- statement:
--   The Formal Local construction uses the iter y Ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L480-L484
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L480-L484

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

theorem MohP3.FormalLocal.iter_yOrd (F : Sk k) (s : ℕ) (i : Fin 8) :
    YOrd ((iter k F (s + 1)).2.1 i) (s - 30) := by sorry
