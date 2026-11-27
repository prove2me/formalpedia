-- Prove2me | Theorems.Thm_MohP3_FormalLocal_wOrd_ffS
-- name    : MohP3.FormalLocal.wOrd_ffS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:14.820047+00:00
-- url     : https://prove2.me/theorems/14bfe1fd-6a95-5820-a1bd-f9ac6baac9c5
-- title:
--   Formal Local: w Ord ff S
-- statement:
--   The Formal Local construction uses the w Ord ff S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L109-L154
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L109-L154

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
omit [CharZero k]

theorem MohP3.FormalLocal.wOrd_ffS (j : Fin 4) : WOrd (ffS k j) (Gen.tau j) := by sorry
