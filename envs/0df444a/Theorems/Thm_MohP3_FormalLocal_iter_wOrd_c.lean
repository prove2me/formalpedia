-- Prove2me | Theorems.Thm_MohP3_FormalLocal_iter_wOrd_c
-- name    : MohP3.FormalLocal.iter_wOrd_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:26.766498+00:00
-- url     : https://prove2.me/theorems/4d4d1632-fa58-590b-9f45-584289389be9
-- title:
--   Formal Local: iter w Ord c
-- statement:
--   The Formal Local construction uses the iter w Ord c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L486-L490
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L486-L490

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

theorem MohP3.FormalLocal.iter_wOrd_c (F : Sk k) (s : ℕ) (j : Fin 4) :
    WOrd ((iter k F (s + 1)).2.2 j) (s - 30) := by sorry
