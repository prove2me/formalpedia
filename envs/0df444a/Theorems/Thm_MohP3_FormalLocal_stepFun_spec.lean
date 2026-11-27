-- Prove2me | Theorems.Thm_MohP3_FormalLocal_stepFun_spec
-- name    : MohP3.FormalLocal.stepFun_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:56.182562+00:00
-- url     : https://prove2.me/theorems/d7a8db9f-4076-4610-ac80-432089091e53
-- title:
--   Formal Local: step Fun spec
-- statement:
--   The Formal Local construction uses the step Fun spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L461-L468
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L461-L468

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

theorem MohP3.FormalLocal.stepFun_spec (n : ℕ) (F : Sk k) (h : WOrd F n) :
    WOrd (stepFun k n F).1 (n + 1) ∧
      (∀ i, YOrd ((stepFun k n F).2.1 i) (n - Gen.sig i)) ∧
      (∀ j, WOrd ((stepFun k n F).2.2 j) (n - Gen.tau j)) ∧
      F - (stepFun k n F).1 =
        (∑ i, iotaS k ((stepFun k n F).2.1 i) * hhS k i) + ∑ j, (stepFun k n F).2.2 j * ffS k j := by sorry
